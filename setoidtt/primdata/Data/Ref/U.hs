
module Data.Ref.U where

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
new a b = Ref <$> UM.new @a 1 a
{-# inline new #-}

read :: forall a b. (Unlifted a) => Ref a b -> IO a
read (Ref arr) = UM.read arr 0
{-# inline read #-}

write :: forall a b. (Unlifted a) => Ref a b -> a -> IO ()
write (Ref arr) a = UM.write arr 0 a
{-# inline write #-}

modify :: forall a b. Unlifted a => Ref a b -> (a -> a) -> IO ()
modify (Ref arr) f = UM.modify arr 0 f
{-# inline modify #-}
