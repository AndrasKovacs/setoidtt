{-# options_ghc -Wno-unused-imports #-}
{-# language Strict #-}

module Parser where

import Data.Char

import Language.Haskell.TH

import qualified Data.ByteString as B
import FlatParse hiding (Parser, runParser, testParser, string, char, switch)
import qualified FlatParse
import Data.Char

import Presyntax
import Lexer

--------------------------------------------------------------------------------

identStartChar :: Parser ()
identStartChar = satisfyA_ isLatinLetter <|> do
  c <- anyChar
  if isGreekLetter c then
    pure ()
  else if c == ' ' || c == '('  || c == ')' then
    empty
  else if isLetter c then
    pure ()
  else
    empty

identChar :: Parser ()
identChar = satisfyA_ (\c -> isLatinLetter c || FlatParse.isDigit c) <|> do
  c <- anyChar
  if isGreekLetter c then
    pure ()
  else if c == ' ' || c == '('  || c == ')' then
    empty
  else if isAlphaNum c then
    pure ()
  else
    empty

pRawIdent :: Parser ()
pRawIdent = identStartChar >> many_ identChar

-- TODO: don't repeat keywords here and in pAtom. Group keywords as atomic and non-atomic.
pKeyword :: Parser ()
pKeyword = $(FlatParse.switch [| case _ of
  "let"  -> pure ()
  "in"   -> pure ()
  "λ"    -> pure ()
  "Set"  -> pure ()
  "Prop" -> pure () |])

-- OPTIMIZE TODO: try alternate "fast-path" identifier parsing
pIdent :: Parser Span
pIdent = lexeme do
  spanned pRawIdent \_ span -> do
    br (inSpan span (pKeyword *> eof))
       empty
       (pure span)

expected :: String -> Parser a
expected thing = err ("expected " ++ thing)
{-# noinline expected #-}

parens :: Parser a -> Parser a
parens p = $(char '(') *> pTm <* $(char ')')

pAtom :: Parser Tm
pAtom =
      (lexeme do
        spanned pRawIdent \_ span -> do
          let kw = inSpan span $(FlatParse.switch [| case _ of
                "Set"  -> eof >> pure (Set span)
                "Prop" -> eof >> pure (Prop span)
                "let"  -> eof >> expected "an atomic expression"
                "in"   -> eof >> expected "an atomic expression"
                "λ"    -> eof >> expected "an atomic expression" |])
          kw <|> pure (Var span))
  <|> (parens pTm)

pTm = undefined
