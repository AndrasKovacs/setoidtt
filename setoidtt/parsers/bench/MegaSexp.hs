
module MegaSexp (run) where

import Control.Applicative
import qualified Data.ByteString as B
import Text.Megaparsec
import Data.Char

type Parser = Parsec () B.ByteString

isLatinLetter :: Char -> Bool
isLatinLetter c = ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')

char8 :: Char -> Parser ()
char8 c = () <$ single (fromIntegral (ord c))

satisfy8 :: (Char -> Bool) -> Parser ()
satisfy8 f = () <$ satisfy (f . chr . fromIntegral)

ws    = skipMany (satisfy8 \c -> c == ' ' || c == '\n')
open  = char8 '(' >> ws
close = char8 ')' >> ws
ident = skipSome (satisfy8 isLatinLetter) <* ws
sexp  = (open *> skipSome sexp <* close) <|> ident
run   = runParser sexp ""
