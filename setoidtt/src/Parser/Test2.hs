
module Parser.Test2 where

import qualified Parser.Internal2 as P
import Gauge

import qualified Text.Megaparsec       as M
import qualified Text.Megaparsec.Char  as M
import qualified Data.Text as T
import qualified Data.ByteString as B

-- import Data.Char

type MParser = M.Parsec String T.Text

bpars' :: MParser ()
bpars' = go >> M.eof where
  go = M.skipMany (M.char '(' >> go >> M.char ')')

bpars :: P.Parser () () ()
bpars = go >> P.eof where
  go = P.many_ (P.charL1 '(' >> go >> P.charL1 ')')

len = 100000 :: Int
inp1 = B.concat $ replicate len "((()))()"
inp2 = T.replicate len "((()))()"

bparsBench :: IO ()
bparsBench = do
  -- print $ M.runParser wsparser "" inp2
  -- print $ runParser (err @String @() "foobar") inp1
  -- print $ runParser ws inp1

  defaultMain [
     -- bench "megaparsec" $ whnf (M.runParser bpars' "") inp2,
     bench "myparser"   $ whnf (P.runParser bpars ()) inp1
     ]
