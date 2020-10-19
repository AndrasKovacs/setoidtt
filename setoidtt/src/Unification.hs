
module Unification where

import Cxt
import Common
import ElabState
import qualified Syntax as S
import qualified Values as V

unifySet :: Cxt -> V.Val -> V.Val -> IO ()
unifySet cxt a a' = undefined
