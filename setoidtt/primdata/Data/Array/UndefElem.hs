
module Data.Array.UndefElem where

import GHC.Stack

undefElem :: forall a. HasCallStack => a
undefElem = error "undefined element"
{-# noinline undefElem #-}
