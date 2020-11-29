
module Serialization.Internal where

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import qualified Data.ByteString.Unsafe as B
import Data.Word
import Foreign.Marshal.Alloc
import GHC.Exts
import GHC.ForeignPtr
import GHC.Types
import Data.Foldable

import qualified Data.Flat as F

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

  default size :: F.Flat a => a -> Int
  size a = F.size @a
  {-# inline size #-}

  default put :: F.Flat a => a -> Put
  put a = Put \p s -> case F.writeOffAddr# p 0# a s of
    s -> (# s, plusAddr# p (F.size# @a proxy#) #)
  {-# inline put #-}

  default get :: F.Flat a => Get a
  get = Get \p -> (# plusAddr# p (F.size# @a proxy#), F.indexOffAddr# p 0# #)
  {-# inline get #-}

instance Serialize Int
instance Serialize Word8

instance Serialize a => Serialize [a] where
  size = foldl' (\acc a -> 1 + acc + size a) 1
  get = do
    get @Word8 >>= \case
      0 -> pure []
      1 -> (:) <$> get <*> get
      _ -> undefined
  put []     = put @Word8 0
  put (a:as) = put @Word8 1 >>. put a >>. put as

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
