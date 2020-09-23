{-# options_ghc -Wno-orphans #-}

module FP
 (
  runSexp,
  runLongws,
  runNumcsv,
  runTm
 ) where

import Old.FlatParse
import Old.Switch

ws      = manyTok_ $(switch [| case _ of "\n" -> pure (); " " -> pure () |])
open    = $(char '(') >> ws
close   = $(char ')') >> ws
ident   = someTok_ (satisfyA isLatinLetter) >> ws
sexp    = br open (some_ sexp >> close) ident
src     = sexp >> eof
runSexp = runParser src

longw     = $(string "thisisalongkeyword")
longws    = someTok_ (longw >> ws) >> eof
runLongws = runParser longws

numeral   = someTok_ (satisfyA \c -> '0' <= c && c <= '9') >> ws
comma     = $(char ',') >> ws
numcsv    = numeral >> manyBr_ comma numeral >> eof
runNumcsv = runParser numcsv

------------------------------------------------------------

type Name = Span
data Tm = Var {-# unpack #-} !Name | Lam {-# unpack #-} !Name !Tm
        | Let {-# unpack #-} !Name !Tm !Tm | App !Tm !Tm

type Parser' = Parser (Pos, String)

instance Show Pos where
  show _ = "pos"

err' :: Pos -> String -> Parser' a
err' !p !str = err (p, str)

bind :: Parser' Span
bind = do
  (i, span) <- spanned (someTok_ (satisfyA isLatinLetter))
  inSpan span do
    p <- getPos
    let kwerr kw = err' p $ "expected an identifier, got a keyword: " ++ kw
    $(switch [| case _ of
        "lam" -> kwerr "lam"
        "let" -> kwerr "let"
        "in"  -> kwerr "in"
        _     -> pure () |])
  ws
  pure span

tok :: Parser' () -> String -> Parser' ()
tok p msg = do
  pos <- getPos
  br p ws (err' pos msg)
{-# inline tok #-}

atom :: Parser' Tm
atom = (Var <$> bind)
   <!> ($(char '(') *> ws *> tm <* $(char ')') <* ws)

tm :: Parser' Tm
tm = $(switch [| case _ of
  "lam" -> do
    ws
    x <- bind
    tok $(char '.') "expected a . in lambda expression"
    t <- tm
    pure (Lam x t)
  "let" -> do
    ws
    x <- bind
    tok $(char '=') "expected a = in let expression"
    t <- tm
    tok $(string "in") "expected an \"in\" in let expression"
    u <- tm
    pure (Let x t u)
  _     -> chainl App atom atom
  |])

runTm = runParser tm
