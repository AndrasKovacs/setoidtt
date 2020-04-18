
{-# LANGUAGE KindSignatures #-}
{-# language MagicHash, UnboxedTuples, BangPatterns, ScopedTypeVariables,
             DeriveAnyClass, RankNTypes, DeriveFunctor, UnboxedSums,
             PatternSynonyms #-}

-- benchmarking whether specialized IO () makes a difference
-- (it doesn't)

import qualified Control.Exception as E
import GHC.Prim
import GHC.Types
import Gauge
import Control.Monad
import Data.Bits

data Tree = Leaf | Node !Tree !Tree

data Ex = Ex
  deriving (Show, E.Exception)

type RW = State# RealWorld

unsafeThrowIO :: forall e a. e -> IO a
unsafeThrowIO e = IO (raiseIO# e)
{-# inline unsafeThrowIO #-}

unsafeCatch :: IO a -> (e -> IO a) -> IO a
unsafeCatch (IO io) f = IO (catch# io (\e -> case f e of IO f -> f))
{-# inline unsafeCatch #-}

full :: Int -> Tree
full 0 = Leaf
full n = let t = full (n - 1) in Node t t

eqPrimE :: Tree -> Tree -> IO Bool
eqPrimE t t' = do
  let go :: Tree -> Tree -> IO ()
      go Leaf       Leaf         = pure ()
      go (Node l r) (Node l' r') = go l l' >> go r r'
      go _          _            = unsafeThrowIO Ex
  (True <$ go t t') `unsafeCatch` \(e :: Ex) -> pure False

eqPrimE' :: Tree -> Tree -> IO Bool
eqPrimE' t t' = do
  let go :: Tree -> Tree -> RW -> RW
      go Leaf       Leaf         s = s
      go (Node l r) (Node l' r') s = go r r' (go l l' s)
      go _          _            s = case raiseIO# Ex s of (# s, _ #) -> s
  IO (\s -> (# go t t' s, True #)) `unsafeCatch` \(e :: Ex) -> pure False

-- No difference at least here.
main :: IO ()
main = do
  let !t = full 24
  defaultMainWith (defaultConfig {displayMode = Condensed}) [
    bench "eqPrimE'" $ whnfIO (eqPrimE' t t),
    bench "eqPrimE"  $ whnfIO (eqPrimE t t),
    bench "eqPrimE'" $ whnfIO (eqPrimE' t t),
    bench "eqPrimE"  $ whnfIO (eqPrimE t t),
    bench "eqPrimE'" $ whnfIO (eqPrimE' t t),
    bench "eqPrimE"  $ whnfIO (eqPrimE t t)

   ]
