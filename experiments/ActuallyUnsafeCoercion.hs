{-# language MagicHash, UnboxedTuples, TypeApplications #-}

import GHC.Prim
import GHC.Types
import GHC.Magic

seq' :: a -> b -> b
seq' a b = seq a b
{-# noinline seq' #-}

main :: IO ()
main = do
  let arr :: ByteArray#
      arr = runRW# $ \s -> case newByteArray# 0# s of
           (# s, marr #) -> case unsafeFreezeByteArray# marr s of
             (# s, arr #) -> arr
      arr' :: Any @(TYPE 'LiftedRep)
      arr' = unsafeCoerce# arr

  print $ seq' arr' True -- throws RTS exception
