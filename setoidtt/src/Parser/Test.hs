
module Parser.Test where

import qualified Parser.Internal2 as P
import Gauge

import qualified Text.Megaparsec as M
import qualified Text.Megaparsec.Char.Lexer as LM
import qualified Data.Text as T
import qualified Data.ByteString as B

-- import Data.Char

type MParser = M.Parsec String T.Text

wsparser :: MParser ()
wsparser = LM.space
  (M.skipSome (M.satisfy \c -> c == ' ' || c == '\n'))
  (LM.skipLineComment "--")
  (LM.skipBlockComment "{-" "-}")

lineCStart =
  P.charL1 '-' >> P.charL1 '-'

blockCStart =
  P.charL1 '{' >> P.charL1 '-'

blockCEnd =
  P.charL1 '-' >> P.charL1 '}'

lineComment =
  lineCStart >> P.many_ (P.satisfy P.Default (/='\n'))

blockComment =
  blockCStart >> P.manyTill_ P.anyChar_ blockCEnd

spaces =
  P.some_ (P.satisfyL1 P.Default (\c -> c == ' ' || c == '\n'))

ws :: P.Parser Int () ()
ws =
  P.many_ (spaces P.<|> lineComment P.<|> blockComment)

len  = 100000
inp1 = B.concat $ replicate len " --foobaaar\n"
inp2 = T.replicate len " --foobaaar\n"

wsBench :: IO ()
wsBench = do
  -- print $ M.runParser wsparser "" inp2
  -- print $ runParser (err @String @() "foobar") inp1
  -- print $ runParser ws inp1

  defaultMain [
     bench "megaparsec" $ whnf (M.runParser wsparser "") inp2,
     bench "myparser"   $ whnf (P.runParser ws (10000 :: Int)) inp1
     ]
