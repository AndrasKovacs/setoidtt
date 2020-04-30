
module ParsersSexp (run) where

import Parsers

ws     = many_ (satisfyL1 Default \c -> c == ' ' || c == '\n')
open   = $(char '(') >> ws
close  = $(char ')') >> ws
ident  = some_ (satisfyL1 Default isLatinLetter) <* ws
sexp   = (open *> some_ sexp <* close) <|> ident
src    = sexp <* eof
run    = runParser src ()
