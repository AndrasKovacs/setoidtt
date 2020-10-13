
{-# language
  BangPatterns, Strict, DeriveGeneric, FlexibleInstances, LambdaCase,
  TypeApplications
  #-}

module Main where

import Data.Compact
import Data.Compact.Serialize
import Data.Binary
import qualified Data.Persist as P
import qualified Data.ByteString as B
import qualified Serialize as S
import qualified SerializeStrict as SS

import Gauge

data Tree a = Leaf a | Node (Tree a) (Tree a)
  deriving (Show)

instance Binary (Tree Int) where
  put (Leaf a)   = put True >> put a
  put (Node l r) = put False >> put l >> put r
  get = do
    get >>= \case
      True -> Leaf <$> get
      False -> Node <$> get <*> get

instance S.Serialize (Tree Int) where
  size t = go t 0 where
    go (Leaf n)   acc = acc + S.size n + 1
    go (Node l r) acc = go l (go r (acc + 1))
  put (Leaf n)   = S.put @Word8 0 S.>>. S.put n
  put (Node l r) = S.put @Word8 1 S.>>. S.put l S.>>. S.put r
  get = do
    S.get @Word8 >>= \case
      0 -> Leaf <$> S.get
      1 -> Node <$> S.get <*> S.get
      _ -> undefined

instance SS.Serialize (Tree Int) where
  size t = go t 0 where
    go (Leaf n)   acc = acc + SS.size n + 1
    go (Node l r) acc = go l (go r (acc + 1))
  put (Leaf n)   = SS.put @Word8 0 SS.>>. SS.put n
  put (Node l r) = SS.put @Word8 1 SS.>>. SS.put l SS.>>. SS.put r
  get = do
    SS.get @Word8 >>= \case
      0 -> Leaf <$> SS.get
      1 -> Node <$> SS.get <*> SS.get
      _ -> undefined

instance P.Persist (Tree Int) where
  put (Leaf a)   = P.put @Word8 0 >> P.put a
  put (Node l r) = P.put @Word8 1 >> P.put l >> P.put r
  get = do
    P.get @Word8 >>= \case
      0 -> Leaf <$> P.get
      1 -> Node <$> P.get <*> P.get
      _ -> undefined

full :: Int -> Tree Int
full 0 = Leaf 128000
full n = let t = full (n - 1) in Node t t

main :: IO ()
main = do
  let t = full 21 :: Tree Int
  defaultMain [
      bench "compact region write" $ whnfIO $ do
        r <- compact t
        writeCompact "compact.tree" r

    , bench "compact region read" $ whnfIO $ do
        unsafeReadCompact @(Tree Int) "compact.tree"

    , bench "Data.Binary write" $ whnfIO $ do
        encodeFile "binary.tree" t

    , bench "Data.Binary read" $ whnfIO $ do
        decodeFile @(Tree Int) "binary.tree"

    , bench "Serialize write" $ whnfIO $ do
        S.toFile "serialize.tree" t

    , bench "Serialize read" $ whnfIO $ do
        S.fromFile @(Tree Int) "serialize.tree"

    , bench "persist write" $ whnfIO $ do
        B.writeFile "persist.tree" $ P.encode t

    , bench "persist read" $ whnfIO $ do
        bstr <- B.readFile "persist.tree"
        pure $ P.decode @(Tree Int) bstr

    , bench "Strict Serialize write" $ whnfIO $ do
        SS.toFile "serialize.tree" t

    , bench "Strict Serialize read" $ whnfIO $ do
        SS.fromFile @(Tree Int) "serialize.tree"

    ]
