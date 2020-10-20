
module Errors where

import Common
import Cxt.Types
import Syntax
import qualified Presyntax as P

data ElabError
  = UnifyError Tm Tm
  | NameNotInScope RawName
  | NoSuchField RawName
  | NoSuchArgument RawName
  | IcitMismatch Icit Icit
  | NoNamedLambdaInference
  | ExpectedSg Tm
  deriving Show

data ElabEx = ElabEx {-# unpack #-} Cxt P.Tm ElabError
  deriving Show
