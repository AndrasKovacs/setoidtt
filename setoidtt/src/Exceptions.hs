
module Exceptions where

import GHC.Prim
import GHC.Types
import GHC.Stack
import qualified Control.Exception as Ex

throwIO :: forall a. Ex -> IO a
throwIO e = IO (raiseIO# e)
{-# inline throwIO #-}

throw :: forall a. Ex -> a
throw = raise#
{-# inline throw #-}

catch :: forall a. IO a -> (Ex -> IO a) -> IO a
catch (IO io) f = IO (catch# io (\e -> case f e of IO f -> f))
{-# inline catch #-}

-- | This is a dirty hack which ensures that our monomorphized `catch` can also
--   catch every standard `Control.Exception` exception potentially thrown by
--   external library code or standard throwing operations such as incomplete
--   matches or zero division. The trick is that the first variant in `Ex` has
--   the same representation as the `Control.Exception` definition, and casing
--   also works because of pointer tagged constructors.  Why do we use this
--   hack? The reason is performance: we use exceptions internally for control
--   flow purposes, and avoiding the standard `Typeable` safety mechanism
--   reduces overheads significantly.
data Ex =
    forall e. Ex.Exception e => SomeException e -- ^ Standard exceptions.
  | ExControl Int -- ^ Compact `Int`-coded exceptions for control flow implementation.
  | ExError       -- ^ Exceptions for actual elaboration errors.

-- | Don't let any non-standard `Ex` exception escape. This should be used on
--   the top of the main function of the program.
fenceEx :: HasCallStack => IO a -> IO a
fenceEx act = act `catch` \case
  SomeException e -> Ex.throw e
  _               -> error "impossible"
