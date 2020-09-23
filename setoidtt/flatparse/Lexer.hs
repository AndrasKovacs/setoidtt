{-# language Strict #-}

module Lexer where

import FlatParse hiding (Parser, runParser, testParser, string, char, switch)
import qualified FlatParse

import Language.Haskell.TH
import qualified Data.ByteString as B

--------------------------------------------------------------------------------

type ParseError = String
type Parser = FlatParse.Parser Int ParseError

runParser :: Parser a -> B.ByteString -> Result ParseError a
runParser p = FlatParse.runParser p 0 0

testParser :: Parser a -> String -> Result ParseError a
testParser p = FlatParse.testParser p 0 0

-- OPTIMIZATION TODO:
--  - try to read space in chunks (2/4)
--  - implement another set of ws/comment functions which don't modify columns,
--    only call the column-adjusting code after newlines
ws :: Parser ()
ws = $(FlatParse.switch [| case _ of
  " "  -> modify (+1) >> ws
  "\n" -> put 0 >> ws
  "\t" -> modify (+1) >> ws
  "\r" -> modify (+1) >> ws
  "--" -> lineComment
  "{-" -> modify (+2) >> multilineComment
  _    -> pure () |])

lineComment :: Parser ()
lineComment =
  br $(FlatParse.char '\n') (put 0 >> ws) $
  br anyChar_ (modify (+1) >> lineComment) $
  pure ()

multilineComment :: Parser ()
multilineComment = $(FlatParse.switch [| case _ of
  "\n" -> put 0 >> multilineComment
  "-}" -> modify (+2) >> ws
  _    -> br anyChar_ (modify (+1) >> multilineComment) $ pure () |])

indentError :: ParseError
indentError = "indentation error"

indentedAt :: Int -> Parser a -> Parser a
indentedAt level p = do
  actual <- get
  if actual == level then p else err indentError
{-# inline indentedAt #-}

nonIndented :: Parser a -> Parser a
nonIndented = indentedAt 0
{-# inline nonIndented #-}

lexeme :: Parser a -> Parser a
lexeme p = do
  lvl <- ask
  currentLvl <- get
  if currentLvl < lvl
    then err indentError
    else p <* ws
{-# inline lexeme #-}

char :: Char -> Q Exp
char c = [| lexeme $(FlatParse.char c) |]

string :: String -> Q Exp
string str = [| lexeme $(FlatParse.string str) |]

switch :: Q Exp -> Q Exp
switch exp = [| do
  lvl <- ask
  currentLvl <- get
  if currentLvl < lvl
    then err indentError
    else $(FlatParse.switch' (Just [| ws |]) exp) |]
