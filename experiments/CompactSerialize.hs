{-# language
  BangPatterns, Strict, DeriveGeneric, FlexibleInstances, LambdaCase,
  TypeApplications #-}

import Data.Compact
import Data.Compact.Serialize
import Data.Time.Clock
import Data.Binary
import GHC.Generics
import qualified Data.Persist as P
import qualified Data.ByteString as B
import Data.Word

data Tree a = Leaf a | Node (Tree a) (Tree a)
  deriving (Show, Generic, Eq)

instance Binary (Tree Int) where
  put (Leaf a)   = put True >> put a
  put (Node l r) = put False >> put l >> put r
  get = do
    get >>= \case
      True -> Leaf <$> get
      False -> Node <$> get <*> get

instance P.Persist (Tree Int) where
  put (Leaf a)   = P.put @Word8 0 >> P.put a
  put (Node l r) = P.put @Word8 1 >> P.put l >> P.put r
  get = do
    P.get @Word8 >>= \case
      0 -> Leaf <$> P.get
      1 -> Node <$> P.get <*> P.get

-- instance Binary (Tree Int)

full :: Int -> Tree Int
full 0 = Leaf 128000
full n = let t = full (n - 1) in Node t t

timed :: String -> IO a -> IO a
timed msg ma = do
  t1 <- getCurrentTime
  a <- ma
  t2 <- getCurrentTime
  putStrLn (msg ++ " " ++ show (diffUTCTime t2 t1))
  pure a

main :: IO ()
main = do
  let t = full 21 :: Tree Int
  timed "compact region write" $ do
    r <- compact t
    writeCompact "compact.tree" r

  timed "compact region read" $ do
    unsafeReadCompact @(Tree Int) "compact.tree"

  timed "Data.Binary write" $ do
    encodeFile "binary.tree" t

  timed "Data.Binary read" $ do
    r <- decodeFile @(Tree Int) "binary.tree"
    case r of Node{} -> print "foo"; _ -> print "kek"

  timed "persist write" $ do
    B.writeFile "persist.tree" $ P.encode t

  timed "persist read" $ do
    bstr <- B.readFile "persist.tree"
    case P.decode @(Tree Int) bstr of
      Left{} -> print "foo"
      _      -> print "kek"
