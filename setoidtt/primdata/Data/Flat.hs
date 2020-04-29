
module Data.Flat (
  Flat(..), size
  ) where

{-|
A class for types which can be naturally represented as uniform-sized pointer-free
values.
-}

import Data.MachDeps
import GHC.Int
import GHC.Prim
import GHC.Types
import GHC.Word

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

#define derivePrim(ty, ctr, sz, idx_arr, rd_arr, wr_arr, idx_addr, rd_addr, wr_addr) \
instance Flat (ty) where {                                      \
  size# _ = (case sz of I# sz -> sz)                            \
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
derivePrim(Word, W#, sIZEOF_WORD,
           indexWordArray#, readWordArray#, writeWordArray#,
           indexWordOffAddr#, readWordOffAddr#, writeWordOffAddr#)
derivePrim(Double, D#, sIZEOF_DOUBLE,
           indexDoubleArray#, readDoubleArray#, writeDoubleArray#,
           indexDoubleOffAddr#, readDoubleOffAddr#, writeDoubleOffAddr#)
derivePrim(Char, C#, sIZEOF_CHAR,
           indexWideCharArray#, readWideCharArray#, writeWideCharArray#,
           indexWideCharOffAddr#, readWideCharOffAddr#, writeWideCharOffAddr#)
derivePrim(Word8, W8#, sIZEOF_WORD8,
           indexWord8Array#, readWord8Array#, writeWord8Array#,
           indexWord8OffAddr#, readWord8OffAddr#, writeWord8OffAddr#)
derivePrim(Word16, W16#, sIZEOF_WORD16,
           indexWord16Array#, readWord16Array#, writeWord16Array#,
           indexWord16OffAddr#, readWord16OffAddr#, writeWord16OffAddr#)
derivePrim(Word32, W32#, sIZEOF_WORD32,
           indexWord32Array#, readWord32Array#, writeWord32Array#,
           indexWord32OffAddr#, readWord32OffAddr#, writeWord32OffAddr#)
derivePrim(Word64, W64#, sIZEOF_WORD64,
           indexWord64Array#, readWord64Array#, writeWord64Array#,
           indexWord64OffAddr#, readWord64OffAddr#, writeWord64OffAddr#)
derivePrim(Int8, I8#, sIZEOF_INT8,
           indexInt8Array#, readInt8Array#, writeInt8Array#,
           indexInt8OffAddr#, readInt8OffAddr#, writeInt8OffAddr#)
derivePrim(Int16, I16#, sIZEOF_INT16,
           indexInt16Array#, readInt16Array#, writeInt16Array#,
           indexInt16OffAddr#, readInt16OffAddr#, writeInt16OffAddr#)
derivePrim(Int32, I32#, sIZEOF_INT32,
           indexInt32Array#, readInt32Array#, writeInt32Array#,
           indexInt32OffAddr#, readInt32OffAddr#, writeInt32OffAddr#)
derivePrim(Int64, I64#, sIZEOF_INT64,
           indexInt64Array#, readInt64Array#, writeInt64Array#,
           indexInt64OffAddr#, readInt64OffAddr#, writeInt64OffAddr#)
