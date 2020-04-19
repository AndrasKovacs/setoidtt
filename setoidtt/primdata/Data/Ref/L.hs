
module Data.Ref.L where

import GHC.Prim
import GHC.Types
import GHC.Magic
import Data.Unlifted

type role Ref representational
data Ref a = Ref (MutVar# RealWorld a)

instance Unlifted (Ref a) where
  toUnlifted# (Ref r) = unsafeCoerce# r
  {-# inline toUnlifted# #-}
  fromUnlifted# r     = Ref (unsafeCoerce# r)
  {-# inline fromUnlifted# #-}
  default# = runRW# (\s -> case newMutVar# (error "undefined element") s of
    (# s , r #) -> Ref r)
  {-# noinline default# #-}

new :: a -> IO (Ref a)
new a = IO (\s -> case newMutVar# a s of
  (# s , r #) -> (# s, Ref r #))
{-# inline new #-}

write :: Ref a -> a -> IO ()
write (Ref r) a = IO (\s -> case writeMutVar# r a s of s -> (# s, () #))
{-# inline write #-}

read :: Ref a -> IO a
read (Ref r) = IO (readMutVar# r)
{-# inline read #-}

modify :: Ref a -> (a -> a) -> IO ()
modify (Ref r) f = IO (\s -> case readMutVar# r s of
  (# s, a #) -> case writeMutVar# r (f a) s of
    s -> (# s, () #))
{-# inline modify #-}

modify' :: Ref a -> (a -> a) -> IO ()
modify' (Ref r) f = IO (\s -> case readMutVar# r s of
  (# s, a #) -> let !a' = f a in case writeMutVar# r a' s of
    s -> (# s, () #))
{-# inline modify' #-}
