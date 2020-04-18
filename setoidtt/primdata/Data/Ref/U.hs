
module Data.Ref.U where

import GHC.Prim
import GHC.Types

import Data.Unlifted

type role Ref representational
data Ref a = Ref (MutVar# RealWorld Any)

instance Unlifted (Ref a) where
  toUnlifted# (Ref r) = unsafeCoerce# r
  {-# inline toUnlifted# #-}
  fromUnlifted# r = Ref (unsafeCoerce# r)
  {-# inline fromUnlifted# #-}

new :: forall a. Unlifted a => a -> IO (Ref a)
new a = case toUnlifted# a of
  a -> IO (\s -> case newMutVar# (unsafeCoerce# a) s of
    (# s , r #) -> (# s, Ref r #))
{-# inline new #-}

write :: forall a. Unlifted a => Ref a -> a -> IO ()
write (Ref r) a = case toUnlifted# a of
  a -> IO (\s -> case writeMutVar# r (unsafeCoerce# a) s of s -> (# s, () #))
{-# inline write #-}

read :: forall a. Unlifted a => Ref a -> IO a
read (Ref r) = IO $ \s -> case readMutVar# r s of
  (# s, a #) -> case fromUnlifted# (unsafeCoerce# a) of
    !a -> (# s, a #)
{-# inline read #-}

modify :: Unlifted a => Ref a -> (a -> a) -> IO ()
modify (Ref r) f = IO (\s -> case readMutVar# r s of
  (# s, a #) -> case fromUnlifted# (unsafeCoerce# a) of
    !a -> case f a of
      !a -> case toUnlifted# a of
        a -> case writeMutVar# r (unsafeCoerce# a) s of
          s -> (# s, () #))
{-# inline modify #-}
