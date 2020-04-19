
module Data.Unlifted (Unlifted(..)) where
import GHC.Prim

-- | Class for type which are isomorphic to an unlifted type. NOTE: the result
--   of `toUnlifted#` must always be bound in a case expression, if we later
--   `unsafeCoerce#` it to a lifted type. Otherwise GHC would try to create a
--   thunk for it, which is not unlifted anymore! Officially, coercion from an
--   unlifted to a lifted type is not supported, and not safe.
--   Also, the result of `fromUnlifted#` should be forced as well; it is
--   safe to not force it, but not optimally efficient, because `fromUnlifted#`
--   pretty much always runs in constant time.
--
--   We also need a default value for the purpose of initializing arrays, because
--   it is not possible to use any "error" thunk for this purpose safely.
class Unlifted a where
  toUnlifted#   :: a -> ArrayArray#
  fromUnlifted# :: ArrayArray# -> a
  default#      :: a
