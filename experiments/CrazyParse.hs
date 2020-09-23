
{-# language LambdaCase, BlockArguments, Strict, DeriveFunctor, DeriveFoldable,
    DeriveTraversable, FlexibleContexts #-}
{-# options_ghc -Wincomplete-patterns #-}

module CrazyCheck where

import Control.Monad
import Control.Monad.Reader
import Data.Char
import Data.Maybe
import Data.Void
import Text.Megaparsec
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

--------------------------------------------------------------------------------

chainl :: M a -> (a -> M a) -> M a
chainl ma f = do
  a <- ma
  let go a = f a <|> pure a
  go a

--------------------------------------------------------------------------------

type Name = String

data Tm
  = Var Name
  | App Tm Tm
  | Lam Name Tm
  | Pi Name Tm Tm
  | U
  | Let Name Tm Tm Tm
  | Sg Name Tm Tm
  | Pair Tm Tm
  | Proj1 Tm
  | Proj2 Tm
  | ProjField Tm Name Int
  | Top
  | Tt
  deriving Show

data Val
  = VVar Name
  | VApp Val ~Val
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU
  | VSg Name Val (Val -> Val)
  | VPair ~Val ~Val
  | VProj1 Val
  | VProj2 Val
  | VProjField Val Name Int
  | VTop
  | VTt

type Env = [(Name, Maybe Val)]

projField :: Val -> Name -> Int -> Val
projField t x i = case (t, i) of
  (VPair t u, 0) -> t
  (VPair t u, i) -> projField u x (i - 1)
  _              -> VProjField t x i

app :: Val -> Val -> Val
app t ~u = case t of
  VLam _ t -> t u
  _        -> VApp t u

proj1 :: Val -> Val
proj1 = \case
  VPair t u -> t
  t         -> VProj1 t

proj2 :: Val -> Val
proj2 = \case
  VPair t u -> t
  t         -> VProj2 t

eval :: Env -> Tm -> Val
eval env = go where
  go = \case
    Var x           -> fromMaybe (VVar x) $ fromJust $ lookup x env
    App t u         -> app (go t) (go u)
    Lam x t         -> VLam x \u -> goBind x u t
    Pi x a b        -> VPi x (go a) \u -> goBind x u b
    U               -> VU
    Let x a t u     -> goBind x (go t) u
    Sg x a b        -> VSg x (go a) \u -> goBind x u b
    Pair t u        -> VPair (go t) (go u)
    Proj1 t         -> proj1 (go t)
    Proj2 t         -> proj2 (go t)
    ProjField t x i -> projField (go t) x i
    Top             -> VTop
    Tt              -> VTt

  goBind x u t = eval ((x, Just u):env) t

fresh :: Env -> Name -> Name
fresh env x = case lookup x env of
  Nothing -> x
  _       -> fresh env (x ++ "'")

conv :: Env -> Val -> Val -> Bool
conv env = go where
  go (VVar x)           (VVar x')            = x == x'
  go (VApp t u)         (VApp t' u')         = go t t' && go u u'
  go (VLam x t)         (VLam x' t')         = goBind x t t'
  go (VPi x a b)        (VPi x' a' b')       = go a a' && goBind x b b'
  go VU                 VU                   = True
  go (VSg x a b)        (VSg x' a' b')       = go a a' && goBind x b b'
  go (VPair t u)        (VPair t' u')        = go t t' && go u u'
  go (VProj1 t)         (VProj1 t')          = go t t'
  go (VProj2 t)         (VProj2 t')          = go t t'
  go (VProjField t _ i) (VProjField t' _ i') = go t t' && i == i'
  go _                  _                    = False

  goBind x t t' =
    let x' = fresh env x
        v  = VVar x'
    in conv ((x', Nothing):env) (t v) (t' v)

--------------------------------------------------------------------------------

data Names = Node Bool [(Char, Names)]
  deriving Show

noNames :: Names
noNames = Node False []

insert :: Name -> Names -> Names
insert [] (Node _ ns) = Node True ns
insert (c:cs) (Node b ns) = Node b (go ns) where
  go []           = [(c, insert cs noNames)]
  go ((c', n):ns) | c == c'   = (c', insert cs n):ns
                  | otherwise = (c', n)          :go ns

inNames :: Name -> Names -> Bool
inNames []     (Node b _ ) = b
inNames (c:cs) (Node _ ns) = maybe False (inNames cs) (lookup c ns)

ctrl :: String
ctrl = "()\\.:=→"

keywords :: Names
keywords = foldr insert noNames ["let", "in", "U", "λ", "->"]

data Cxt = Cxt {
  _types     :: [(Name, Val)],
  _env       :: Env,
  _indentLvl :: Int,
  _names     :: Names}

bind :: Name -> Val -> Cxt -> Cxt
bind x ~a (Cxt as env l ns) =
  Cxt ((x, a):as) ((x, Nothing):env) l (insert x ns)

define :: Name -> Val -> Val -> Cxt -> Cxt
define x ~a ~t (Cxt as env l ns) =
  Cxt ((x, a):as) ((x, Just t):env) l (insert x ns)

binding :: Name -> Val -> M a -> M a
binding x ~a = local (bind x a)

defining :: Name -> Val -> Val -> M a -> M a
defining x ~a ~t = local (define x a t)

evalM :: Tm -> M Val
evalM t = asks ((`eval` t) . _env)

type M = ParsecT Void String (Reader Cxt)

ws :: M ()
ws = skipMany (satisfy isSpace)

char :: Char -> M ()
char c = () <$ (C.char c <* ws)

string :: String -> M ()
string s = () <$ (C.string s <* ws)

ident :: M Name
ident = do
  str <- some (satisfy \c -> not (isSpace c) && not (elem c ctrl)) <* ws
  when (inNames str keywords) (fail "expected a binder, got a keyword")
  pure str

var :: M Name
var = do
  ns <- asks _names
  let go :: Names -> M Name
      go (Node b ns) =
        foldr (\(c, ns) acc -> ((c:) <$> (C.char c >> go ns)) <|> acc)
              (if b then pure "" else empty)
              ns
  x <- go ns
  when (inNames x keywords) (fail "expected a binder, got a keyword")
  pure x

iVar :: M (Tm, Val)
iVar = do
  x  <- var
  ts <- asks _types
  case lookup x ts of
    Nothing -> error $ "variable not in scope: " ++ x
    Just a  -> pure (Var x, a)

iAtom :: M (Tm, Val)
iAtom = iVar
    <|> (char '(' *> infer <* char ')')
    <|> ((U, VU) <$ char 'U')

cAtom :: Val -> M Tm
cAtom ~a = iVar
    <|> (char '(' *> infer <* char ')')
    <|> ((U, VU) <$ char 'U')


iApps :: M (Tm, Val)
iApps = chainl iAtom \(t, a) -> do
  case a of
    VPi x a b -> do
      u <- check a
      _
    _ -> pure (t, a)


iLam :: M (Tm, Val)
iLam =
  (char 'λ' <|> char '\\') >> error "cannot infer type for lambda"

iLet :: M (Tm, Val)
iLet = do
  string "let"
  x <- ident
  char ':'
  a <- check VU
  ~va <- evalM a
  char '='
  t <- check va
  ~vt <- evalM t
  string "in"
  defining x va vt do
    (u, b) <- infer
    pure (Let x a t u, b)

iPi :: M (Tm, Val)
iPi = do
  char '('
  x <- ident
  char ':'
  a <- check VU
  char ')'
  char '→'
  ~av <- evalM a
  binding x av do
    b <- check VU
    pure (Pi x a b, VU)

infer :: M (Tm, Val)
infer = iLam <|> iLet <|> iPi <|> iApps

check :: Val -> M Tm
check = undefined
