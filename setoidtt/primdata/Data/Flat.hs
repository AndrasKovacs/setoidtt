
module Data.Flat (
  Flat(..), size
  ) where

import GHC.Prim
import GHC.Types
import Data.MachDeps

class Flat a where

  -- | Size of values of type @a@.
  size# :: Proxy# a -> Int#

  -- | Read a value from the array. The offset is in elements of type
  -- @a@ rather than in bytes.
  indexByteArray# :: ByteArray# -> Int# -> a

  -- | Read a value from the mutable array. The offset is in elements of type
  -- @a@ rather than in bytes.
  readByteArray# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, a #)

  -- | Write a value to the mutable array. The offset is in elements of type
  -- @a@ rather than in bytes.
  writeByteArray# :: MutableByteArray# s -> Int# -> a -> State# s -> State# s

  -- | Read a value from a memory position given by an address and an offset.
  -- The memory block the address refers to must be immutable. The offset is in
  -- elements of type @a@ rather than in bytes.
  indexOffAddr# :: Addr# -> Int# -> a

  -- | Read a value from a memory position given by an address and an offset.
  -- The offset is in elements of type @a@ rather than in bytes.
  readOffAddr# :: Addr# -> Int# -> State# s -> (# State# s, a #)

  -- | Write a value to a memory position given by an address and an offset.
  -- The offset is in elements of type @a@ rather than in bytes.
  writeOffAddr# :: Addr# -> Int# -> a -> State# s -> State# s

size :: forall a. Flat a => Int
size = I# (size# @a proxy#)
{-# inline size #-}

unI# :: Int -> Int#
unI# (I# n#) = n#

#define derivePrim(ty, ctr, sz, idx_arr, rd_arr, wr_arr, idx_addr, rd_addr, wr_addr) \
instance Flat (ty) where {                                      \
  size# _ = unI# sz                                             \
; indexByteArray# arr# i# = ctr (idx_arr arr# i#)               \
; readByteArray#  arr# i# s# = case rd_arr arr# i# s# of        \
                        { (# s1#, x# #) -> (# s1#, ctr x# #) }  \
; writeByteArray# arr# i# (ctr x#) s# = wr_arr arr# i# x# s#    \
; indexOffAddr# addr# i# = ctr (idx_addr addr# i#)              \
; readOffAddr#  addr# i# s# = case rd_addr addr# i# s# of       \
                        { (# s1#, x# #) -> (# s1#, ctr x# #) }  \
; writeOffAddr# addr# i# (ctr x#) s# = wr_addr addr# i# x# s#   \
; {-# inline size# #-}                                          \
; {-# inline indexByteArray# #-}                                \
; {-# inline readByteArray# #-}                                 \
; {-# inline writeByteArray# #-}                                \
; {-# inline indexOffAddr# #-}                                  \
; {-# inline readOffAddr# #-}                                   \
; {-# inline writeOffAddr# #-}                                  \
}


derivePrim(Int, I#, sIZEOF_INT,
           indexIntArray#, readIntArray#, writeIntArray#,
           indexIntOffAddr#, readIntOffAddr#, writeIntOffAddr#)
derivePrim(Double, D#, sIZEOF_DOUBLE,
           indexDoubleArray#, readDoubleArray#, writeDoubleArray#,
           indexDoubleOffAddr#, readDoubleOffAddr#, writeDoubleOffAddr#)
derivePrim(Char, C#, sIZEOF_CHAR,
           indexWideCharArray#, readWideCharArray#, writeWideCharArray#,
           indexWideCharOffAddr#, readWideCharOffAddr#, writeWideCharOffAddr#)
