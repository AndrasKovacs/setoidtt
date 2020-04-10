
module Parser (
    parseString
  , parseStdin
  ) where

import Control.Monad
import Data.Char
import Data.Void
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Set as S

import Types

--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos' :: Parser a -> Parser (SPos, a)
withPos' p = (,) <$> (SPos <$> getSourcePos) <*> p

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> (SPos <$> getSourcePos) <*> p

lexeme   = L.lexeme ws
symbol s = lexeme (C.string s)
char c   = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
braces p = char '{' *> p <* char '}'
pArrow   = symbol "→" <|> symbol "->"
pBind    = pIdent <|> symbol "_"

keywords :: S.Set String
keywords = S.fromList [
  "let", "in", "λ", "Set", "Prop", "trans",
  "⊤",   "tt", "⊥", "exfalso", "Eq", "refl", "coe", "sym", "ap"]

pIdent :: Parser Name
pIdent = try $ do
  start <- takeWhile1P Nothing isAlphaNum
  rest  <- takeWhileP Nothing (\c -> isAlphaNum c || c == '\'' || c == '-')
  let x = start ++ rest
  when (S.member x keywords) $
    fail (printf "Expected an identifier, but \"%s\" is a keyword." x)
  x <$ ws

pAtom :: Parser Raw
pAtom  =
      withPos (    (RVar     <$> pIdent          )
               <|> (RSet     <$  symbol "Set"    )
               <|> (RProp    <$  symbol "Prop"   )
               <|> (RTop     <$  symbol "⊤"      )
               <|> (RBot     <$  symbol "⊥"      )
               <|> (RTt      <$  symbol "tt"     )
               <|> (RExfalso <$  symbol "exfalso")
               <|> (REq      <$  symbol "Eq"     )
               <|> (RRefl    <$  symbol "refl"   )
               <|> (RCoe     <$  symbol "coe"    )
               <|> (RSym     <$  symbol "sym"    )
               <|> (RTrans   <$  symbol "trans"  )
               <|> (RAp      <$  symbol "ap"     )
               <|> (RHole    <$  char   '_'      ))

  <|> do {
        char '(';
        t1 <- pTm;
        optional (char ',') >>= \case
            Nothing -> char ')' >> pure t1
            Just{}  -> do {t2 <- pTm; char ')'; pure (RPair t1 t2)}
        }

pProj :: Parser (SPos, RProj)
pProj =
  withPos' (
      (RProj1 <$ symbol ".₁")
  <|> (RProj2 <$ symbol ".₂")
  <|> (RProjField <$> (C.char '.' *> pIdent)))

-- application or projection
pArg :: Parser (Either (Icit,Raw) (SPos, RProj))
pArg = (Right <$> pProj)
   <|> (Left . (Impl,) <$> (char '{' *> pTm <* char '}'))
   <|> (Left. (Expl,) <$> pAtom)

pSpine :: Parser Raw
pSpine = do
  h    <- pAtom
  args <- many pArg
  pure $ foldl (\t -> either (\(i, u) -> RApp t u i)
                             (\(pos, p) -> RSrcPos pos (RProj t p)))
         h args

pLamBinder :: Parser (Name, Maybe Raw, Icit)
pLamBinder =
      ((,Nothing,Expl) <$> pBind)
  <|> parens ((,,Expl) <$> pBind <*> optional (char ':' *> pTm))
  <|> (braces ((,,Impl) <$> pBind <*> optional (char ':' *> pTm)))

pLam :: Parser Raw
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pTm
  pure $ foldr (\(x, a, ni) t -> RLam x a ni t) t xs

pPiBinder :: Parser ([Name], Raw, Icit)
pPiBinder =
      braces ((,,Impl) <$> some pBind
                       <*> ((char ':' *> pTm) <|> pure RHole))
  <|> parens ((,,Expl) <$> some pBind
                       <*> (char ':' *> pTm))
pPi :: Parser Raw
pPi = do
  dom <- some pPiBinder
  pArrow
  cod <- pTm
  pure $ foldr (\(xs, a, i) t -> foldr (\x -> RPi x i a) t xs) cod dom

pSg :: Parser Raw
pSg = do
  (x, a) <- parens ((,) <$> pBind <*> (char ':' *> pTm))
  char '×'
  b <- pTm
  pure (RSg x a b)

pFunOrSpineOrPair :: Parser Raw
pFunOrSpineOrPair = do
  sp <- pSpine
  optional pArrow >>= \case
    Just _  -> RPi "_" Expl sp <$> pTm
    Nothing -> optional (symbol "×") >>= \case
      Just _  -> RSg "_" sp <$> pTm
      Nothing -> pure sp

pLet :: Parser Raw
pLet = do
  symbol "let"
  x <- pIdent
  ann <- optional (char ':' *> pTm)
  char '='
  t <- pTm
  symbol "in"
  u <- pTm
  pure $ RLet x (maybe RHole id ann) t u

pTm :: Parser Raw
pTm = withPos (pLam <|> pLet <|> try pPi <|> try pSg <|> pFunOrSpineOrPair)

pSrc :: Parser Raw
pSrc = ws *> pTm <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  src <- getContents
  t <- parseString src
  pure (t, src)
