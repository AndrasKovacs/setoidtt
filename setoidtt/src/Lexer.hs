
module Lexer where

import FlatParse hiding (Parser, runParser, testParser, string, char, switch, cut, err)
import qualified FlatParse

import Language.Haskell.TH
import qualified Data.ByteString as B

--------------------------------------------------------------------------------

data ParseError = ParseError Pos String deriving Show
type Parser = FlatParse.Parser Int ParseError

runParser :: Parser a -> B.ByteString -> Result ParseError a
runParser p = FlatParse.runParser p 0 0

showError :: String -> B.ByteString -> ParseError -> String
showError path str (ParseError pos msg) = let
  (!l, !c) = posLineCol str pos
  lnum     = show l
  lpad     = map (const ' ') lnum
  lines    = linesUTF8 str
  in case lines of
    [] -> "empty input"
    _  ->
      let line = (lines !! l)
      in   path ++ ":" ++ show l ++ ":" ++ show c ++ ":" ++ "\n"
        ++ lpad ++ " |\n"
        ++ lnum ++ " | " ++ line ++ "\n"
        ++ lpad ++ " | " ++ replicate c ' ' ++ "^\n"
        ++ msg
{-# noinline showError #-}

testParser :: Show a => Parser a -> String -> IO ()
testParser p str = let
  bstr = packUTF8 str
  in case FlatParse.testParser p 0 0 bstr of
         OK a _ _ -> print a
         Fail     -> putStrLn "parser failure"
         Err e    -> putStrLn (showError "(stdin)" bstr e)
{-# noinline testParser #-}

cut :: Parser a -> String -> Parser a
cut (FlatParse.Parser f) msg = FlatParse.Parser \r eob s n -> case f r eob s n of
  Fail# -> Err# (ParseError (addr2Pos# eob s) msg)
  x     -> x
{-# inline cut #-}

err :: String -> Parser a
err msg = FlatParse.Parser \r eob s n -> Err# (ParseError (addr2Pos# eob s) msg)
{-# inline err #-}

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

-- TODO: nested multiline comments
multilineComment :: Parser ()
multilineComment = $(FlatParse.switch [| case _ of
  "\n" -> put 0 >> multilineComment
  "-}" -> modify (+2) >> ws
  _    -> br anyChar_ (modify (+1) >> multilineComment) $ pure () |])

checkIndent :: Parser ()
checkIndent = do
  lvl <- ask
  currentLvl <- get
  if currentLvl < lvl
    then empty
    else pure ()
{-# inline checkIndent #-}

lexeme :: Parser a -> Parser a
lexeme p = checkIndent *> p <* ws
{-# inline lexeme #-}

char :: Char -> Q Exp
char c = [| lexeme $(FlatParse.char c) |]

string :: String -> Q Exp
string str = [| lexeme $(FlatParse.string str) |]

switch :: Q Exp -> Q Exp
switch exp = [| do
  checkIndent
  $(FlatParse.switch' (Just [| ws |]) exp) |]
