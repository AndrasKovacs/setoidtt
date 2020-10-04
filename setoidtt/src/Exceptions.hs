
module Exceptions (
  Conv(..), type Ex, throwIO, throw, catch, fenceEx
  ) where

import GHC.Prim
import GHC.Types
import GHC.Stack
import qualified Control.Exception as Ex

import Common
import Syntax

throwIO# :: forall a. Ex# -> IO a
throwIO# e = IO (raiseIO# e)
{-# inline throwIO# #-}

throw# :: forall a. Ex# -> a
throw# = raise#
{-# inline throw# #-}

catch# :: forall a. IO a -> (Ex# -> IO a) -> IO a
catch# (IO io) f = IO (GHC.Prim.catch# io (\e -> case f e of IO f -> f))
{-# inline catch# #-}

data Conv
  = CSame
  | CDiff
  | CMeta Meta
  | CUMax UMax

type Ex = Conv

throwIO :: Ex -> IO a
throwIO e = throwIO# (Ex# e)
{-# inline throwIO #-}

throw :: Ex -> a
throw e = throw# (Ex# e)
{-# inline throw #-}

exThrow :: Ex.Exception e => e -> a
exThrow = Ex.throw
{-# noinline exThrow #-}

catch :: IO a -> (Ex -> IO a) -> IO a
catch ma f = ma `Exceptions.catch#` \case
  SomeException e -> exThrow e
  Ex# e           -> f e
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
data Ex# =
    forall e. Ex.Exception e => SomeException e -- ^ Standard exceptions.
  | Ex# Ex

-- | Don't let any non-standard `Ex` exception escape. This should be used on
--   the top of the main function of the program.
fenceEx :: HasCallStack => IO a -> IO a
fenceEx act = act `Exceptions.catch#` \case
  SomeException e -> Ex.throw e
  _               -> error "impossible"
