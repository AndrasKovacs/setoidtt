
module Parser (pTm, pSrc, parseFile, Result(..)) where

import Control.Monad
import Data.Char
import Data.Foldable
import FlatParse hiding (Parser, runParser, testParser, string, char, switch, cut, err)
import qualified FlatParse       as FP
import qualified Data.ByteString as B

import Common
import Presyntax
import Lexer

--------------------------------------------------------------------------------

{-

TODO: update grammar with fully applied builtins

Precedences from strongest to weakest:
  - atoms
  - projections            (postfix)
  - function application   (left assoc)
  - equality type          (infix, no assoc)
  - sigma                  (right assoc)
  - lam/let                (right assoc)
  - pairs                  (right assoc)

Context-free grammar (disregarding indentation!)

  builtin     = "Set" | "Prop"
              | "refl" | "sym" | "trans" | "coe" | "ap"
              | "⊤" | "tt"
              | "⊥" | "exfalso"

  identifier  = <non-empty string of alphanumeric characters, starting with a letter>
  binder      = identifier | "_"
  arrow       = "->" | "→"
  pibinder    = "{" (binder)+ : term "}" | "(" (binder)+ : term ")" | "{" (binder)+ "}"
  lambda      = "λ" | "\"
  times       = "×" | "*"
  lambinder   = binder | "{" binder "}" | "{" identifier "=" identifier "}"

  atom        = builtin | identifier | "_" | "(" term ")" |
  projection  = atom | projection ".₁" | projection ".₂" | projection "." identifier
  application = projection | application projection | application "{" term "}" | application "{" identifier "=" term "}"
  equality    = application | application "=" application
  sigma       = equality | equality "×" sigma | "(" binder : term ")" "×" sigma
  pi          = sigma | sigma arrow pi | (pibinder)+ arrow pi
  lamLet      = pi | lambda (lambinder)+ "." lamLet
                | "let" identifier ":=" pair "in" lamLet
                | "let" identifier ":" pair ":=" pair in lamLet
  pair        = lamLet | lamLet "," pair
  term        = pair

  topDef      = identifier ":" term ":=" term | identifier ":=" term
  postulate   = identifier ":" term
  program     = "" | topDef program | postulate program

Indentation:
  - every topDef or postulate identifier must be non-indented
  - every topDef or postulate type/definition must be indented (cannot have a lexeme at column 0)
  - top-level entries are delimited by indentation in implementation

-}

--------------------------------------------------------------------------------

identStartChar :: Parser ()
identStartChar =
  () <$ satisfy' isLatinLetter isGreekLetter isLetter isLetter
{-# inline identStartChar #-}

identChar :: Parser ()
identChar =
  () <$ satisfy' (\c -> isLatinLetter c || FlatParse.isDigit c) isGreekLetter isAlphaNum isAlphaNum

inlineIdentChar :: Parser ()
inlineIdentChar =
  () <$ satisfy' (\c -> isLatinLetter c || FlatParse.isDigit c) isGreekLetter isAlphaNum isAlphaNum
{-# inline inlineIdentChar #-}

manyIdents :: Parser ()
manyIdents = many_ inlineIdentChar

skipToSpan :: Pos -> Parser Span
skipToSpan l = br identChar
  (do {manyIdents; r <- getPos; ws; pure (Span l r)})
  empty
{-# inline skipToSpan #-}

pIdent :: Parser Span
pIdent = do
  checkIndent
  l <- getPos
  $(FP.switch [| case _ of
    "let"     -> skipToSpan l
    "in"      -> skipToSpan l
    "λ"       -> skipToSpan l
    "Set"     -> skipToSpan l
    "Prop"    -> skipToSpan l
    "trans"   -> skipToSpan l
    "sym"     -> skipToSpan l
    "refl"    -> skipToSpan l
    "coe"     -> skipToSpan l
    "ap"      -> skipToSpan l
    "⊤"       -> skipToSpan l
    "tt"      -> skipToSpan l
    "⊥"       -> skipToSpan l
    "exfalso" -> skipToSpan l
    _         -> do {identStartChar; manyIdents; r <- getPos; ws; pure (Span l r)} |])

pBind :: Parser Bind
pBind = (Bind <$> pIdent) <|> (DontBind <$ ($(FP.char '_') >> ws))

pArrow :: Parser ()
pArrow = $(switch [| case _ of
  "->" -> pure ()
  "→"  -> pure () |])

pTimes :: Parser ()
pTimes = $(switch [| case _ of
  "×" -> pure ()
  "*" -> pure () |])

pColon  = $(char ':')
pParL   = $(char '(')
pParR   = $(char ')')
pBraceL = $(char '{')
pBraceR = $(char '}')
pComma  = $(char ',')
pDot    = $(char '.')
pIn     = $(string "in")
pEq     = $(char '=')
pAssign = $(string ":=")

--------------------------------------------------------------------------------

skipToVar :: Pos -> (Pos -> Parser Tm) -> Parser Tm
skipToVar l p = br identChar
  (do {manyIdents; r <- getPos; ws; pure $ Var (Span l r)})
  (do {r <- getPos; ws; p r})
{-# inline skipToVar #-}

pAtomicExp :: Parser Tm
pAtomicExp = do
  checkIndent
  l <- getPos
  $(FP.switch [| case _ of
    "("       -> ws *> pTm <* pParR `cut` "expected a \")\" in parenthesized expression"
    "_"       -> do {r <- getPos; ws; pure $ Hole (Span l r)}
    "let"     -> skipToVar l \_ -> empty
    "in"      -> skipToVar l \_ -> empty
    "λ"       -> skipToVar l \_ -> empty
    "exfalso" -> skipToVar l \_ -> empty
    "coe"     -> skipToVar l \_ -> empty
    "sym"     -> skipToVar l \_ -> empty
    "trans"   -> skipToVar l \_ -> empty
    "ap"      -> skipToVar l \_ -> empty
    "refl"    -> skipToVar l \r -> pure (Refl (Span l r) Nothing Nothing)
    "Set"     -> skipToVar l \r -> pure (Set (Span l r))
    "Prop"    -> skipToVar l \r -> pure (Prop (Span l r))
    "⊤"       -> skipToVar l \r -> pure (Top (Span l r))
    "tt"      -> skipToVar l \r -> pure (Tt (Span l r))
    "⊥"       -> skipToVar l \r -> pure (Bot (Span l r))
    _         -> do {identChar; manyIdents; r <- getPos; ws; pure (Var (Span l r))} |])

--------------------------------------------------------------------------------

goProj :: Tm -> Parser Tm
goProj t = br pDot
  (checkIndent >> $(FP.switch [|case _ of
      "₁" -> do {p <- getPos; ws; goProj (Proj1 t p)}
      "1" -> do {p <- getPos; ws; goProj (Proj1 t p)}
      "₂" -> do {p <- getPos; ws; goProj (Proj2 t p)}
      "2" -> do {p <- getPos; ws; goProj (Proj2 t p)}
      _   -> do {x <- pIdent `cut` "expected a field projection"; goProj (ProjField t x)}|]))
  (pure t)

pProjExp :: Parser Tm
pProjExp = do
  t <- pAtomicExp `cut` "expected \"(\", \"_\", \"refl\", \"Set\", \"Prop\", \"⊤\", \"tt\", \"⊥\" or an identifier"
  goProj t

--------------------------------------------------------------------------------

goApp :: Tm -> Parser Tm
goApp t = br pBraceL
  (do optioned (pIdent <* pAssign)
        (\x -> do
          u <- pTm
          pBraceR `cut` "expected \"}\" in implicit application"
          goApp (App t u (Named x)))
        (do
          u <- pTm
          pBraceR `cut` "expected \"}\" in implicit application"
          goApp (App t u (NoName Impl))))
  (do optioned pAtomicExp
        (\u -> do
          u <- goProj u
          goApp (App t u (NoName Expl)))
        (pure t))

mArg :: Parser (Maybe Tm)
mArg = br pBraceL
  (do u <- pTm
      pBraceR `cut` "expected \"}\" in implicit application"
      pure $ Just u)
  (pure Nothing)

skipToApp :: Pos -> (Pos -> Parser Tm) -> Parser Tm
skipToApp l p = br identChar
  (do {manyIdents; r <- getPos; ws; goApp =<< goProj (Var (Span l r))})
  (do {r <- getPos; ws; p r})
{-# inline skipToApp #-}

pAppExp :: Parser Tm
pAppExp = do
  checkIndent
  l <- getPos
  $(FP.switch [| case _ of
    "exfalso" ->
      skipToApp l \_ ->
      goApp =<< (Exfalso l <$> mArg <*> pProjExp) `cut` "expected an argument for exfalso"
    "refl"    ->
      skipToApp l \r ->
      goApp =<< (Refl (Span l r) <$> mArg <*> mArg)
    "coe"     ->
      skipToApp l \_ ->
      goApp =<< (Coe l <$> mArg <*> mArg <*> pProjExp <*> pProjExp) `cut` "expected two arguments for coe"
    "sym"     ->
      skipToApp l \_ ->
      goApp =<< (Sym l <$> mArg <*> mArg <*> mArg <*> pProjExp) `cut` "expected an argument to sym"
    "trans"   ->
      skipToApp l \_ ->
      goApp =<< (Trans l <$> mArg <*> mArg <*> mArg <*> mArg <*> pProjExp <*> pProjExp) `cut` "expected two arguments for trans"
    "ap"      ->
      skipToApp l \_ ->
      goApp =<< (Ap l <$> mArg <*> mArg <*> pProjExp <*> mArg <*> mArg <*> pProjExp) `cut` "expected two arguments for ap"
    _         ->
      goApp =<< pProjExp |])


--------------------------------------------------------------------------------

-- TODO: prefix (=) as well!
pEqExp :: Parser Tm
pEqExp = do
  t <- pAppExp
  br pEq (Eq t <$> pAppExp) (pure t)

--------------------------------------------------------------------------------

pSigmaExp :: Parser Tm
pSigmaExp = do
  pos <- getPos
  optioned (pParL *> pBind <* pColon)
    (\x -> do
      a <- pTm
      pParR           `cut` "expected \")\" in sigma binder"
      pTimes          `cut` "expected \"×\" or \"*\" after binder in sigma type expression"
      b <- pSigmaExp
      pure $ Sg pos x a b)
    (do
      t <- pEqExp
      br pTimes (Sg pos DontBind t <$> pSigmaExp) (pure t))

--------------------------------------------------------------------------------

-- OPTIMIZE TODO: eliminate the intermediate list and structures, use instead CPS.
-- FIXME: the "spanned" in pImplPiBinder is wonky because it includes the trailing whitespace
--        (the optimized solution with precise lookahead should also return the correct span)

pExplPiBinder :: Parser ([Bind], Tm, Icit)
pExplPiBinder = do
  binders <- some pBind
  pColon
  a <- pTm
  pParR `cut` "expected \")\" in implicit argument binder"
  pure (binders, a, Expl)

pImplPiBinder :: Parser ([Bind], Tm, Icit)
pImplPiBinder =
    spanned (some pBind) \binders span -> do
      br pColon
        ((binders,,Impl) <$> (pTm <* braceClose))
        ((binders, Hole span, Impl) <$ braceClose)
  where
    braceClose = pBraceR  `cut` "expected \"}\" in implicit argument binder"

pPiBinder :: Parser ([Bind], Tm, Icit)
pPiBinder = $(switch [| case _ of
  "(" -> pExplPiBinder
  "{" -> pImplPiBinder
  |])

pPiExp :: Parser Tm
pPiExp = do
  pos <- getPos
  optioned (some pPiBinder)
    (\case
        -- pi/sigma ambiguity resolution
        [([x], a, Expl)] -> $(switch [| case _ of
          "->" -> Pi pos x Expl a <$> pPiExp
          "→"  -> Pi pos x Expl a <$> pPiExp
          "*"  -> do dom <- Sg pos x a <$> pSigmaExp;
                     br pArrow (Pi pos DontBind Expl dom <$> pPiExp) (pure dom)
          "×"  -> do dom <- Sg pos x a <$> pSigmaExp;
                     br pArrow (Pi pos DontBind Expl dom <$> pPiExp) (pure dom)
          _    -> err "expected \"->\", \"→\", \"×\" or \"*\" after binder" |])
        binders -> do
          pArrow        `cut` "expected \"->\" or \"→\" in function type"
          b <- pPiExp
          pure $!
            foldr' (\(xs, a, i) t -> foldr' (\x b -> Pi pos x i a b) t xs)
                   b binders)
    (do
      t <- pSigmaExp
      br pArrow
        (Pi pos DontBind Expl t <$> pPiExp)
        (pure t))

--------------------------------------------------------------------------------

-- TODO: reduce duplication, perhaps with some higher-order combinator
pLam' :: Parser Tm
pLam' = do
  pos <- getPos
  $(switch [| case _ of
       "{" -> pBind >>= \case
         DontBind -> Lam pos DontBind (NoName Impl) <$> pLam'
         Bind x   -> br pAssign
           (do y <- pIdent `cut` "expected an identifier"
               pBraceR `cut` "expected \"}\""
               Lam pos (Bind y) (Named x) <$> pLam')
           (do pBraceR `cut` "expected \"}\""
               Lam pos (Bind x) (NoName Impl) <$> pLam')
       "." -> do
         pLamLetExp
       _ -> do
         x <- pBind `cut` "expected a binder or \".\""
         Lam pos x (NoName Expl) <$> pLam'
       |])

pLam :: Pos -> Parser Tm
pLam pos = $(switch [| case _ of
  "{" -> pBind >>= \case
    DontBind -> Lam pos DontBind (NoName Impl) <$> pLam'
    Bind x  -> br pAssign
      (do y <- pIdent `cut` "expected an identifier"
          pBraceR `cut` "expected \"}\""
          Lam pos (Bind y) (Named x) <$> pLam')
      (do pBraceR `cut` "expected \"}\""
          Lam pos (Bind x) (NoName Impl) <$> pLam')
  _ -> do
    x <- pBind `cut` "expected a binder"
    Lam pos x (NoName Expl) <$> pLam' |])

pLet :: Pos -> Parser Tm
pLet pos = do
  x <- pIdent `cut` "expected an identifier"
  $(switch [| case _ of
    ":=" -> do
      t <- pTm
      pIn `cut` "expected \"in\" in let-expression"
      u <- pLamLetExp
      pure $ Let pos x Nothing t u
    ":"  -> do
      a <- pTm
      pAssign `cut` "expected \":=\" in let-expression"
      t <- pTm
      pIn `cut` "expected \"in\" in let-expression"
      u <- pLamLetExp
      pure $ Let pos x (Just a) t u
    _    -> err "expected \":\" or \":=\" in let-expression"  |])

pLamLetExp :: Parser Tm
pLamLetExp = do
  checkIndent
  l <- getPos
  $(FP.switch [| case _ of
    "λ"   -> skipToApp l \_ -> pLam l
    "\\"  -> ws >> pLam l
    "let" -> skipToApp l \_ -> pLet l
    _     -> ws >> pPiExp |])

--------------------------------------------------------------------------------

pTm :: Parser Tm
pTm = do
  t <- pLamLetExp
  br pComma (Pair t <$> pTm) (pure t)

--------------------------------------------------------------------------------


topIndentErr :: Parser a
topIndentErr = err "top-level definitions should be non-indented"

pTopLevel :: Parser TopLevel
pTopLevel =
  -- top entry
      (do lvl <- get
          pos <- getPos
          x   <- pIdent <* modify (+1)
          when (lvl /= 0) (setPos pos >> topIndentErr)
          local (const 1)
            $(switch [| case _ of
              ":=" -> Define x Nothing <$> pTm <*> local (const 0) pTopLevel
              ":"  -> do a <- pTm
                         br pAssign
                           (Define x (Just a) <$> pTm <*> local (const 0) pTopLevel)
                           (Postulate x a <$> local (const 0) pTopLevel)
              _    -> err "expected \":\" or \":=\" in top-level binding" |]))

  -- end of file
  <|> (do pos <- getPos
          $(switch [| case _ of
             ":=" -> setPos pos >> topIndentErr
             ":"  -> setPos pos >> topIndentErr
             _    -> (eof `cut` "expected end of file") >> pure Presyntax.Nil |]))

pSrc :: Parser TopLevel
pSrc = ws *> pTopLevel

--------------------------------------------------------------------------------

parseFile :: FilePath -> IO TopLevel
parseFile path = do
  src <- B.readFile path
  case runParser pSrc src of
    OK a _ _ -> pure a
    Fail     -> impossible
    Err e    -> putStrLn (showError path src e) >> error "parse error"
