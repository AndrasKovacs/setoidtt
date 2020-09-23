

module FPEF
 (
  runSexp,
  runLongws,
  runNumcsv
 )
 where

import FlatParse

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
runSexp = runParser src () 0

longw     = $(string "thisisalongkeyword")
longws    = some_ (longw >> ws) >> eof
runLongws = runParser longws () 0


numeral   = some_ (satisfyA \c -> '0' <= c && c <= '9') >> ws
comma     = $(char ',') >> ws
numcsv    = numeral >> many_ (comma >> numeral) >> eof
runNumcsv = runParser numcsv () 0
