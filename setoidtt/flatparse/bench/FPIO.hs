
module FPIO
 (
  runSexp,
  runLongws,
  runNumcsv
 )
 where

import Old.FlatParseIO

ws      = many_ do
            ensureBytes# 1
            c <- scanAny8#
            case c of
              32 -> pure ()
              10 -> pure ()
              _  -> empty

open    = $(char '(') >> ws
close   = $(char ')') >> ws
ident   = some_ (satisfyA isLatinLetter) >> ws
sexp    = br open (some_ sexp >> close) ident
src     = sexp >> eof
runSexp = runParser src

longw     = $(string "thisisalongkeyword")
longws    = someBr_ longw ws >> eof
runLongws = runParser longws

numeral   = some_ (satisfyA \c -> '0' <= c && c <= '9') >> ws
comma     = $(char ',') >> ws
numcsv    = numeral >> manyBr_ comma numeral >> eof
runNumcsv = runParser numcsv
