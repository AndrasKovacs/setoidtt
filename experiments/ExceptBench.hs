{-# language MagicHash, UnboxedTuples, BangPatterns, ScopedTypeVariables,
             DeriveAnyClass, RankNTypes, DeriveFunctor #-}

-- benchmarking various exception mechanisms
-- module ExceptBench where

import qualified Control.Exception as E
import GHC.Prim
import GHC.Types
import Gauge
import Control.Monad
import Data.Bits

data Tree = Leaf | Node !Tree !Tree
  deriving Show

data Ex = Ex
  deriving (Show, E.Exception)

unsafeThrowIO :: forall e a. e -> IO a
unsafeThrowIO e = IO (raiseIO# e)
{-# inline unsafeThrowIO #-}

unsafeCatch :: IO a -> (e -> IO a) -> IO a
unsafeCatch (IO io) f = IO (catch# io (\e -> case f e of IO f -> f))
{-# inline unsafeCatch #-}

full :: Int -> Tree
full 0 = Leaf
full n = let t = full (n - 1) in Node t t

eqBool :: Tree -> Tree -> Bool
eqBool Leaf       Leaf         = True
eqBool (Node l r) (Node l' r') = eqBool l l' && eqBool r r'
eqBool _          _            = False

eqBool2 :: Tree -> Tree -> Bool
eqBool2 t t' = go t t' == 1 where
  go :: Tree -> Tree -> Int
  go Leaf Leaf = 1
  go (Node l r) (Node l' r') = go l l' .&. go r r'
  go _ _ = 0

eqE :: Tree -> Tree -> IO Bool
eqE t t' = do
  let go :: Tree -> Tree -> IO ()
      go Leaf       Leaf         = pure ()
      go (Node l r) (Node l' r') = go l l' >> go r r'
      go _          _            = E.throwIO Ex
  (True <$ go t t') `E.catch` \(e :: Ex) -> pure False

eqPrimE :: Tree -> Tree -> IO Bool
eqPrimE t t' = do
  let go :: Tree -> Tree -> IO ()
      go Leaf       Leaf         = pure ()
      go (Node l r) (Node l' r') = go l l' >> go r r'
      go _          _            = unsafeThrowIO Ex
  (True <$ go t t') `unsafeCatch` \(e :: Ex) -> pure False

eqMaybe :: Tree -> Tree -> Bool
eqMaybe t t' = maybe False (\_ -> True) (go t t') where
  go Leaf       Leaf         = pure ()
  go (Node l r) (Node l' r') = go l l' >> go r r'
  go _ _                     = Nothing

newtype MaybeC a = MaybeC {runMaybeC :: forall r. r -> (a -> r) -> r}
  deriving Functor

instance Applicative MaybeC where
  pure a = MaybeC $ \n j -> j a
  MaybeC f <*> MaybeC a = MaybeC $ \n j ->
    f n (\f -> a n (\a -> j (f a)))

instance Monad MaybeC where
  return = pure
  MaybeC a >>= f = MaybeC $ \n j ->
    a n (\a -> runMaybeC (f a) n j)

eqMaybeC :: Tree -> Tree -> Bool
eqMaybeC t t' = runMaybeC (go t t') False (\_ -> True) where
  go :: Tree -> Tree -> MaybeC ()
  go Leaf       Leaf         = pure ()
  go (Node l r) (Node l' r') = go l l' >> go r r'
  go _ _                     = MaybeC $ \n j -> n

newtype Cont r a = Cont {runCont :: (a -> r) -> r} deriving Functor

instance Applicative (Cont r) where
  pure a = Cont $ \k -> k a
  Cont f <*> Cont a = Cont $ \k -> f (\f -> a (\a -> k (f a)))

instance Monad (Cont r) where
  return = pure
  Cont a >>= f = Cont $ \k -> a (\a -> runCont (f a) k)

callCC :: forall a r. ((forall b. a -> Cont r b) -> Cont r a) -> Cont r a
callCC act = Cont $ \k -> runCont (act (\a -> Cont $ \_ -> k a)) k
{-# inline callCC #-}

eqCont :: Tree -> Tree -> Bool
eqCont t t' = flip runCont id $ do
  callCC $ \exit -> do
    let go Leaf       Leaf         = pure True
        go (Node l r) (Node l' r') = go l l' >> go r r'
        go _ _                     = exit False
    go t t'

modTree :: Tree -> Tree
modTree = f where
  f Leaf       = Node Leaf Leaf
  f (Node l r) = Node (g l) r
  g Leaf       = Node Leaf Leaf
  g (Node l r) = Node l (f r)

main :: IO ()
main = do
  let !tree1  = full 1
      !tree2  = full 2
      !tree4  = full 4
      !tree10 = full 10
      !tree20 = full 20
      !tree23 = full 23

  let !tree1b  = modTree tree1
      !tree2b  = modTree tree2
      !tree4b  = modTree tree4
      !tree10b = modTree tree10
      !tree20b = modTree tree20
      !tree23b = modTree tree23

  defaultMain [
    bgroup "eq" [
      bgroup "tree1" [
        bench "eqBool"   $ whnf (join eqBool) tree1,
        bench "eqBool2"  $ whnf (join eqBool2) tree1,
        bench "eqMaybe"  $ whnf (join eqMaybe) tree1,
        bench "eqMaybeC" $ whnf (join eqMaybeC) tree1,
        bench "eqCont"   $ whnf (join eqCont) tree1,
        bench "eqE"      $ whnfIO $ eqE tree1 tree1,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree1 tree1],

      bgroup "tree2" [
        bench "eqBool"   $ whnf (join eqBool) tree2,
        bench "eqBool2"  $ whnf (join eqBool2) tree2,
        bench "eqMaybe"  $ whnf (join eqMaybe) tree2,
        bench "eqMaybeC" $ whnf (join eqMaybeC) tree2,
        bench "eqCont"   $ whnf (join eqCont) tree2,
        bench "eqE"      $ whnfIO $ eqE tree2 tree2,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree2 tree2],

      bgroup "tree4" [
        bench "eqBool"   $ whnf (join eqBool) tree4,
        bench "eqBool2"  $ whnf (join eqBool2) tree4,
        bench "eqMaybe"  $ whnf (join eqMaybe) tree4,
        bench "eqMaybeC" $ whnf (join eqMaybeC) tree4,
        bench "eqCont"   $ whnf (join eqCont) tree4,
        bench "eqE"      $ whnfIO $ eqE tree4 tree4,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree4 tree4],

      bgroup "tree10" [
        bench "eqBool"   $ whnf (join eqBool) tree10,
        bench "eqBool2"  $ whnf (join eqBool2) tree10,
        bench "eqMaybe"  $ whnf (join eqMaybe) tree10,
        bench "eqMaybeC" $ whnf (join eqMaybeC) tree10,
        bench "eqCont"   $ whnf (join eqCont) tree10,
        bench "eqE"      $ whnfIO $ eqE tree10 tree10,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree10 tree10],

      bgroup "tree20" [
        bench "eqBool"   $ whnf (join eqBool) tree20,
        bench "eqBool2"  $ whnf (join eqBool2) tree20,
        bench "eqMaybe"  $ whnf (join eqMaybe) tree20,
        bench "eqMaybeC" $ whnf (join eqMaybeC) tree20,
        bench "eqCont"   $ whnf (join eqCont) tree20,
        bench "eqE"      $ whnfIO $ eqE tree20 tree20,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree20 tree20],

      bgroup "tree23" [
        bench "eqBool"   $ whnf (join eqBool) tree23,
        bench "eqBool2"  $ whnf (join eqBool2) tree23,
        bench "eqMaybe"  $ whnf (join eqMaybe) tree23,
        bench "eqMaybeC" $ whnf (join eqMaybeC) tree23,
        bench "eqCont"   $ whnf (join eqCont) tree23,
        bench "eqE"      $ whnfIO $ eqE tree23 tree23,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree23 tree23]],

    bgroup "neq" [
      bgroup "tree1" [
        bench "eqBool"   $ whnf (uncurry eqBool)   (tree1, tree1b),
        bench "eqBool2"  $ whnf (uncurry eqBool2)  (tree1, tree1b),
        bench "eqMaybe"  $ whnf (uncurry eqMaybe)  (tree1, tree1b),
        bench "eqMaybeC" $ whnf (uncurry eqMaybeC) (tree1, tree1b),
        bench "eqCont"   $ whnf (uncurry eqCont)   (tree1, tree1b),
        bench "eqE"      $ whnfIO $ eqE tree1 tree1b,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree1 tree1b],

      bgroup "tree2" [
        bench "eqBool"   $ whnf (uncurry eqBool)   (tree2, tree2b),
        bench "eqBool2"  $ whnf (uncurry eqBool2)  (tree2, tree2b),
        bench "eqMaybe"  $ whnf (uncurry eqMaybe)  (tree2, tree2b),
        bench "eqMaybeC" $ whnf (uncurry eqMaybeC) (tree2, tree2b),
        bench "eqCont"   $ whnf (uncurry eqCont)   (tree2, tree2b),
        bench "eqE"      $ whnfIO $ eqE tree2 tree2b,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree2 tree2b],

      bgroup "tree4" [
        bench "eqBool"   $ whnf (uncurry eqBool)   (tree4, tree4b),
        bench "eqBool2"  $ whnf (uncurry eqBool2)  (tree4, tree4b),
        bench "eqMaybe"  $ whnf (uncurry eqMaybe)  (tree4, tree4b),
        bench "eqMaybeC" $ whnf (uncurry eqMaybeC) (tree4, tree4b),
        bench "eqCont"   $ whnf (uncurry eqCont)   (tree4, tree4b),
        bench "eqE"      $ whnfIO $ eqE tree4 tree4b,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree4 tree4b],

      bgroup "tree10" [
        bench "eqBool"   $ whnf (uncurry eqBool)   (tree10, tree10b),
        bench "eqBool2"  $ whnf (uncurry eqBool2)  (tree10, tree10b),
        bench "eqMaybe"  $ whnf (uncurry eqMaybe)  (tree10, tree10b),
        bench "eqMaybeC" $ whnf (uncurry eqMaybeC) (tree10, tree10b),
        bench "eqCont"   $ whnf (uncurry eqCont)   (tree10, tree10b),
        bench "eqE"      $ whnfIO $ eqE tree10 tree10b,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree10 tree10b],

      bgroup "tree20" [
        bench "eqBool"   $ whnf (uncurry eqBool)   (tree20, tree20b),
        bench "eqBool2"  $ whnf (uncurry eqBool2)  (tree20, tree20b),
        bench "eqMaybe"  $ whnf (uncurry eqMaybe)  (tree20, tree20b),
        bench "eqMaybeC" $ whnf (uncurry eqMaybeC) (tree20, tree20b),
        bench "eqCont"   $ whnf (uncurry eqCont)   (tree20, tree20b),
        bench "eqE"      $ whnfIO $ eqE tree20 tree20b,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree20 tree20b],

      bgroup "tree23" [
        bench "eqBool"   $ whnf (uncurry eqBool)   (tree23, tree23b),
        bench "eqBool2"  $ whnf (uncurry eqBool2)  (tree23, tree23b),
        bench "eqMaybe"  $ whnf (uncurry eqMaybe)  (tree23, tree23b),
        bench "eqMaybeC" $ whnf (uncurry eqMaybeC) (tree23, tree23b),
        bench "eqCont"   $ whnf (uncurry eqCont)   (tree23, tree23b),
        bench "eqE"      $ whnfIO $ eqE tree23 tree23b,
        bench "eqPrimE"  $ whnfIO $ eqPrimE tree23 tree23b]]

      ]
