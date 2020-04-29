
module Data.Ref.UU where

import GHC.Prim
import Data.Unlifted
import qualified Data.Array.UM as UM

type role Ref representational representational
newtype Ref a b = Ref (UM.Array a)

instance (Unlifted a, Unlifted b) => Unlifted (Ref a b) where
  type Rep (Ref a b) = MutableArrayArray# RealWorld
  to# (Ref (UM.Array r)) = r
  {-# inline to# #-}
  from# r = Ref (UM.Array r)
  {-# inline from# #-}
  defaultElem = Ref defaultElem
  {-# inline defaultElem #-}

new :: forall a b. (Unlifted a, Unlifted b) => a -> b -> IO (Ref a b)
new a b = do
  arr <- UM.new @a 2 a
  UM.write @b (unsafeCoerce# arr) 1 b
  pure (Ref (unsafeCoerce# arr))
{-# inline new #-}

readFst :: forall a b. (Unlifted a) => Ref a b -> IO a
readFst (Ref arr) = UM.read arr 0
{-# inline readFst #-}

readSnd :: forall a b. (Unlifted b) => Ref a b -> IO b
readSnd (Ref arr) = UM.read @b (unsafeCoerce# arr) 1
{-# inline readSnd #-}

writeFst :: forall a b. (Unlifted a) => Ref a b -> a -> IO ()
writeFst (Ref arr) a = UM.write arr 0 a
{-# inline writeFst #-}

writeSnd :: forall a b. (Unlifted b) => Ref a b -> b -> IO ()
writeSnd (Ref arr) b = UM.write @b (unsafeCoerce# arr) 1 b
{-# inline writeSnd #-}

modifyFst :: forall a b. Unlifted a => Ref a b -> (a -> a) -> IO ()
modifyFst (Ref arr) f = UM.modify arr 0 f
{-# inline modifyFst #-}

modifySnd :: forall a b. Unlifted b => Ref a b -> (b -> b) -> IO ()
modifySnd (Ref arr) f = UM.modify @b (unsafeCoerce# arr) 1 f
{-# inline modifySnd #-}
