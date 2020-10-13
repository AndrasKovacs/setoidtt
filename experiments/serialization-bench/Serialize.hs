
{-# language MagicHash, Strict, BangPatterns, UnboxedTuples, RankNTypes, BlockArguments,
             TypeApplications, ScopedTypeVariables #-}

module Serialize where

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import qualified Data.ByteString.Unsafe as B
import Foreign.Marshal.Alloc
import GHC.Exts
import GHC.ForeignPtr
import GHC.Types
import GHC.Word

newtype Put = Put {
  runPut :: forall s. Addr# -> State# s -> (# State# s, Addr# #)}

infixr 1 >>.
(>>.) :: Put -> Put -> Put
(>>.) (Put f) (Put g) = Put \p s -> case f p s of
  (# s, p #) -> g p s
{-# inline (>>.) #-}

newtype Get a = Get {
  runGet :: Addr# -> (# Addr#, a #)}

instance Functor Get where
  fmap f (Get g) = Get \p -> case g p of
    (# p, a #) -> let !b = f a in (# p, b #)
  {-# inline fmap #-}

instance Applicative Get where
  pure = return
  {-# inline pure #-}
  Get ff <*> Get fa = Get \p -> case ff p of
    (# p, f #) -> case fa p of
      (# p, a #) -> let !b = f a in (# p, b #)
  {-# inline (<*>) #-}

instance Monad Get where
  return ~a = Get \p -> (# p, a #)
  {-# inline return #-}
  Get f >>= g = Get \p -> case f p of
    (# p, a #) -> runGet (g a) p
  {-# inline (>>=) #-}

class Serialize a where
  size :: a -> Int
  put  :: a -> Put
  get  :: Get a

instance Serialize Int where
  size _ = 8
  {-# inline size #-}
  put (I# n) = Put \p s -> case writeIntOffAddr# p 0# n s of
    s -> (# s, plusAddr# p 8# #)
  {-# inline put #-}
  get = Get \p -> (# plusAddr# p 8#, I# (indexIntOffAddr# p 0#) #)
  {-# inline get #-}

instance Serialize Word8 where
  size _ = 1
  {-# inline size #-}
  put (W8# n) = Put \p s -> case writeWord8OffAddr# p 0# n s of
    s -> (# s, plusAddr# p 1# #)
  {-# inline put #-}
  get = Get \p -> (# plusAddr# p 1#, W8# (indexWord8OffAddr# p 0#) #)
  {-# inline get #-}

toFile :: forall a. Serialize a => FilePath -> a -> IO ()
toFile path a = do
  let s = size a
  allocaBytes s \buf@(Ptr addr) -> do
    fp <- newForeignPtr_  buf
    IO (\s -> case runPut (put a) addr s of
           (# s, buf #) -> (# s, () #))
    B.writeFile path (B.PS fp 0 s)

fromFile :: forall a. Serialize a => FilePath -> IO a
fromFile path = do
  bstr <- B.readFile path
  B.unsafeUseAsCString bstr \(Ptr addr) ->
    case runGet (get @a) addr of
      (# _, a #) -> pure a
