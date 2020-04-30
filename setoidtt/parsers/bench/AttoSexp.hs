
module AttoSexp (run) where

import Control.Applicative
import Data.Attoparsec.ByteString.Char8

isLatinLetter :: Char -> Bool
isLatinLetter c = ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')

ws    = skipMany (satisfy \c -> c == ' ' || c == '\n')
open  = char '(' >> ws
close = char ')' >> ws
ident = skipMany1 (satisfy isLatinLetter) <* ws
sexp  = (open *> skipMany1 sexp <* close) <|> ident
run   = parseOnly sexp
