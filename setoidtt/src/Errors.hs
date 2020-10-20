
module Errors where

import Common
import Syntax
import qualified Presyntax as P

data ElabError
  = UnifyError Tm Tm
  | NameNotInScope {-# unpack #-} RawName
  | NoSuchField {-# unpack #-} RawName
  | NoSuchArgument {-# unpack #-} RawName
  | IcitMismatch Icit Icit
  | NoNamedLambdaInference
  | ExpectedSg Tm
  deriving Show

data ElabEx = ElabEx Locals P.Tm ElabError
  deriving Show
