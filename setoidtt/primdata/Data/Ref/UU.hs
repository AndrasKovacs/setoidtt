
module Data.Ref.UU where

import GHC.Types
import GHC.Prim
import qualified Data.Array.SMU as SMU
import Data.Unlifted
import IO

type role Ref representational representational
newtype Ref a b = Ref (SMU.Array Any)

instance (Unlifted a, Unlifted b) => Unlifted (Ref a b) where
  toUnlifted# (Ref r) = unsafeCoerce# r
  {-# inline toUnlifted# #-}
  fromUnlifted# r = Ref (unsafeCoerce# r)
  {-# inline fromUnlifted# #-}
  default# = runIO $ new Data.Unlifted.default# Data.Unlifted.default#
  {-# inline default# #-}

new :: forall a b. (Unlifted a, Unlifted b) => a -> b -> IO (Ref a b)
new a b = case toUnlifted# a of
  a -> case toUnlifted# b of
    b -> do
      arr <- SMU.new @a 2 (unsafeCoerce# a)
      SMU.write @b (unsafeCoerce# arr) 1 (unsafeCoerce# b)
      pure (Ref (unsafeCoerce# arr))
{-# inline new #-}

readFst :: forall a b. (Unlifted a) => Ref a b -> IO a
readFst (Ref arr) = SMU.read (unsafeCoerce# arr) 0
{-# inline readFst #-}

readSnd :: forall a b. (Unlifted b) => Ref a b -> IO b
readSnd (Ref arr) = SMU.read (unsafeCoerce# arr) 1
{-# inline readSnd #-}

writeFst :: forall a b. (Unlifted a) => Ref a b -> a -> IO ()
writeFst (Ref arr) a = SMU.write (unsafeCoerce# arr) 0 a
{-# inline writeFst #-}

writeSnd :: forall a b. (Unlifted b) => Ref a b -> b -> IO ()
writeSnd (Ref arr) b = SMU.write (unsafeCoerce# arr) 1 b
{-# inline writeSnd #-}

modifyFst :: forall a b. Unlifted a => Ref a b -> (a -> a) -> IO ()
modifyFst (Ref arr) f = SMU.modify (unsafeCoerce# arr) 0 f
{-# inline modifyFst #-}

modifySnd :: forall a b. Unlifted b => Ref a b -> (b -> b) -> IO ()
modifySnd (Ref arr) f = SMU.modify (unsafeCoerce# arr) 1 f
{-# inline modifySnd #-}
