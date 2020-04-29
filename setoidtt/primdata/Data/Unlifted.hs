
module Data.Unlifted where

{-| Class for types that can be represented as elements of TYPE 'UnliftedRep.
    NOTE: this module is unsound to use in FFI:

    https://gitlab.haskell.org/ghc/ghc/issues/16650

    Do not pass any data to FFI which contains some unlifted value coerced to a
    different unlifted type!
-}

import GHC.Prim
import GHC.Types

writeUnlifted# ::
   forall (a :: TYPE 'UnliftedRep) s. MutableArrayArray# s -> Int# -> a -> State# s -> State# s
writeUnlifted# marr i a s = writeArrayArrayArray# marr i (unsafeCoerce# a) s
{-# inline writeUnlifted# #-}

readUnlifted# :: forall (a :: TYPE 'UnliftedRep) s.
         MutableArrayArray# s -> Int# -> State# s -> (# State# s, a #)
readUnlifted# marr i s = unsafeCoerce# (readArrayArrayArray# marr i s)
{-# inline readUnlifted# #-}

indexUnlifted# :: forall (a :: TYPE 'UnliftedRep). ArrayArray# -> Int# -> a
indexUnlifted# arr i = unsafeCoerce# (indexArrayArrayArray# arr i)
{-# inline indexUnlifted# #-}

setUnlifted# ::
  forall (a :: TYPE 'UnliftedRep) s. MutableArrayArray# s -> a -> State# s -> State# s
setUnlifted# marr a s =
  let go :: MutableArrayArray# s -> a -> State# s -> Int# -> Int# -> State# s
      go marr a s l i = case i ==# l of
        1# -> s
        _  -> case writeUnlifted# marr i a s of s -> go marr a s l (i +# 1#)
  in go marr a s (sizeofMutableArrayArray# marr) 0#
{-# inline setUnlifted# #-}

newUnlifted# :: forall (a :: TYPE 'UnliftedRep) s. Int# -> a -> State# s -> (# State# s, MutableArrayArray# s #)
newUnlifted# i a s = case newArrayArray# i s of
  (# s, marr #) -> case setUnlifted# marr a s of
    s -> (# s, marr #)
{-# inline newUnlifted# #-}

class Unlifted (a :: *) where
  type Rep a  :: TYPE 'UnliftedRep
  to#         :: a -> Rep a
  from#       :: Rep a -> a
  defaultElem :: a
