{-# options_ghc -Wno-unused-imports #-}
{-# language Strict #-}

module Parser (pPairExp) where

import Data.Char

import Language.Haskell.TH

import Data.Foldable
import qualified Data.ByteString as B
import FlatParse hiding (Parser, runParser, testParser, string, char, switch, cut, err)
import qualified FlatParse
import Data.Char

import Presyntax
import Lexer

--------------------------------------------------------------------------------

{-
Precedences from strongest to weakest:
  - atoms
  - projections            (postfix)
  - function application   (left assoc)
  - equality type          (infix, no assoc)
  - sigma                  (right assoc)
  - lam/let                (right assoc)
  - pairs                  (right assoc)

Context-free grammar

  builtin     = "Set" | "Prop"
              | "refl" | "sym" | "trans" | "coe" | "ap"
              | "⊤" | "tt"
              | "⊥" | "exfalso"

  identifier  = <non-empty string of alphanumeric characters, starting with a letter>
  arrow       = "->" | "→"
  pibinder    = "{" (identifier)+ : pair "}" | "(" (identifier)+ : pair ")" | "{" (identifier)+ "}"
  lambda      = "λ" | "\"
  times       = "×" | "*"
  lambinder   = identifier | "{" identifier "}" | "{" identifier "=" identifier "}"

  atom        = builtin | identifier | "_" | "(" pair ")" |
  projection  = atom | projection ".₁" | projection ".₂" | projection "." identifier
  application = projection | application projection | application "{" pair "}" | application "{" identifier "=" pair "}"
  equality    = application | application "=" application
  sigma       = equality | equality "×" sigma | "(" identifier : pair ")" "×" sigma
  pi          = sigma | sigma arrow pi | (pibinder)+ arrow pi
  lamLet      = pi | lambda (lambinder)+ "." lamLet
                | "let" identifier ":=" pair "in" lamLet
                | "let" identifier ":" pair ":=" pair in lamLet
  pair        = lamLet | lamLet "," pair
  term        = pair

-}

--------------------------------------------------------------------------------

identStartChar :: Parser ()
identStartChar = satisfyA_ isLatinLetter <|> do
  c <- anyChar
  if c == ' ' || c == '('  || c == ')' then
    empty
  else if isGreekLetter c then
    pure ()
  else if isLetter c then
    pure ()
  else
    empty

identChar :: Parser ()
identChar = satisfyA_ (\c -> isLatinLetter c || FlatParse.isDigit c) <|> do
  c <- anyChar
  if c == ' ' || c == '('  || c == ')' then
    empty
  else if isGreekLetter c then
    pure ()
  else if isAlphaNum c then
    pure ()
  else
    empty

pRawIdent :: Parser ()
pRawIdent = identStartChar >> many_ identChar

-- TODO: don't repeat keywords here and in pAtomicExp. Group keywords as atomic and non-atomic.
pKeyword :: Parser ()
pKeyword = $(FlatParse.switch [| case _ of
  "let"     -> pure ()
  "in"      -> pure ()
  "λ"       -> pure ()
  "Set"     -> pure ()
  "Prop"    -> pure ()
  "trans"   -> pure ()
  "sym"     -> pure ()
  "refl"    -> pure ()
  "coe"     -> pure ()
  "ap"      -> pure ()
  "⊤"       -> pure ()
  "tt"      -> pure ()
  "⊥"       -> pure ()
  "exfalso" -> pure () |])

-- OPTIMIZE TODO: try alternate "fast-path" identifier parsing
pIdent :: Parser Span
pIdent = lexeme do
  spanned pRawIdent \_ span -> do
    br (inSpan span (pKeyword *> eof))
       empty
       (pure span)

pBind :: Parser Bind
pBind = lexeme (
      (Bind <$> (spanned pRawIdent \_ span -> do
        br (inSpan span (pKeyword *> eof))
           empty
           (pure span)))
  <|>
      (DontBind <$ $(FlatParse.char '_')))

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

-- TODO: add matching on eof to FlatParse.switch, then
-- we wouldn't have to do all these br eof-s.
pAtomicExp :: Parser Tm
pAtomicExp = do
  checkIndent
  start <- getPos
  $(FlatParse.switch [| case _ of
      "(" -> ws *> pPairExp <* pParR `cut` "expected a \")\" in parenthesized expression"
      "_" -> do {end <- getPos; Hole (Span start end) <$ ws}
      _   -> do
        res <- spanned pRawIdent \_ span -> inSpan span $(FlatParse.switch [| case _ of
          "let"     -> br eof empty                 (pure (Var span))
          "in"      -> br eof empty                 (pure (Var span))
          "λ"       -> br eof empty                 (pure (Var span))
          "Set"     -> br eof (pure (Set span))     (pure (Var span))
          "Prop"    -> br eof (pure (Prop span))    (pure (Var span))
          "trans"   -> br eof (pure (Trans span))   (pure (Var span))
          "sym"     -> br eof (pure (Sym span))     (pure (Var span))
          "refl"    -> br eof (pure (Refl span))    (pure (Var span))
          "coe"     -> br eof (pure (Coe span))     (pure (Var span))
          "ap"      -> br eof (pure (Ap span))      (pure (Var span))
          "⊤"       -> br eof (pure (Top span))     (pure (Var span))
          "tt"      -> br eof (pure (Tt span))      (pure (Var span))
          "⊥"       -> br eof (pure (Bot span))     (pure (Var span))
          "exfalso" -> br eof (pure (Exfalso span)) (pure (Var span))
          _         ->                              (pure (Var span)) |])
        res <$ ws |])

--------------------------------------------------------------------------------

goProj :: Tm -> Parser Tm
goProj t = br pDot
  (checkIndent >> $(FlatParse.switch [|case _ of
      "₁" -> do {p <- getPos; ws; goProj (Proj1 t p)}
      "1" -> do {p <- getPos; ws; goProj (Proj1 t p)}
      "₂" -> do {p <- getPos; ws; goProj (Proj2 t p)}
      "2" -> do {p <- getPos; ws; goProj (Proj2 t p)}
      _   -> do {x <- pIdent `cut` "expected a field projection"; goProj (ProjField t x)}|]))
  (pure t)

pProjExp :: Parser Tm
pProjExp = do
  t <- pAtomicExp `cut` "expected an atomic expression"
  goProj t

--------------------------------------------------------------------------------

goApp :: Tm -> Parser Tm
goApp t = br pBraceL
  (do optional (pIdent <* pAssign) >>= \case
        Nothing -> do
          u <- pPairExp
          pBraceR `cut` "expected \"}\" in implicit application"
          goApp (App t u (NoName Impl))
        Just x  -> do
          u <- pPairExp
          pBraceR `cut` "expected \"}\" in implicit application"
          goApp (App t u (Named x)))
  (do optional pAtomicExp >>= \case
        Nothing -> pure t
        Just u  -> do
          u <- goProj u
          goApp (App t u (NoName Expl)))

pAppExp :: Parser Tm
pAppExp = do
  t <- pProjExp
  goApp t

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
  optional (pParL *> pBind <* pColon) >>= \case

    Just x -> do
      a <- pPairExp
      pParR           `cut` "expected \")\" in sigma binder"
      pTimes          `cut` "expected \"×\" or \"*\" after binder in sigma type expression"
      b <- pSigmaExp
      pure $ Sg pos x a b

    Nothing -> do
      t <- pEqExp
      br pTimes (Sg pos DontBind t <$> pSigmaExp) (pure t)

--------------------------------------------------------------------------------

-- OPTIMIZE TODO: eliminate the intermediate list and structures, use instead CPS.
-- FIXME: the "spanned" in pImplPiBinder is wonky because it includes the trailing whitespace
--        (the optimized solution with precise lookahead should also return the correct span)

pExplPiBinder :: Parser ([Bind], Tm, Icit)
pExplPiBinder = do
  binders <- some pBind
  pColon
  a <- pPairExp
  pParR `cut` "expected \")\" in implicit argument binder"
  pure (binders, a, Expl)

pImplPiBinder :: Parser ([Bind], Tm, Icit)
pImplPiBinder =
    spanned (some pBind) \binders span -> do
      br pColon
        ((binders,,Impl) <$> (pPairExp <* braceClose))
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
  optional (some pPiBinder) >>= \case

    -- pi/sigma ambiguity resolution
    Just [([x], a, Expl)] -> $(switch [| case _ of
      "->" -> Pi pos x Expl a <$> pPiExp
      "→"  -> Pi pos x Expl a <$> pPiExp
      "*"  -> Sg pos x a <$> pSigmaExp
      "×"  -> Sg pos x a <$> pSigmaExp
      _    -> err "expected \"->\", \"→\", \"×\" or \"*\" after binder" |])

    Just binders -> do
      pArrow        `cut` "expected \"->\" or \"→\" in function type"
      b <- pPiExp
      pure $!
        foldr' (\(xs, a, i) t -> foldr' (\x b -> Pi pos x i a b) t xs)
               b binders

    Nothing -> do
      t <- pSigmaExp
      br pArrow
        (Pi pos DontBind Expl t <$> pPiExp)
        (pure t)

--------------------------------------------------------------------------------


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
      t <- pPairExp
      pIn `cut` "expected \"in\" in let-expression"
      u <- pLamLetExp
      pure $ Let pos x Nothing t u
    ":"  -> do
      a <- pPairExp
      pAssign `cut` "expected \":=\" in let-expression"
      t <- pPairExp
      pIn `cut` "expected \"in\" in let-expression"
      u <- pLamLetExp
      pure $ Let pos x (Just a) t u
    _    -> err "expected \":\" or \":=\" in let-expression"  |])

pLamLetExp :: Parser Tm
pLamLetExp = do
  pos <- getPos
  $(switch [| case _ of
    "λ"   -> pLam pos
    "\\"  -> pLam pos
    "let" -> pLet pos
    _     -> pPiExp |])

--------------------------------------------------------------------------------

pPairExp :: Parser Tm
pPairExp = do
  t <- pLamLetExp
  br pComma (Pair t <$> pPairExp) (pure t)

--------------------------------------------------------------------------------
