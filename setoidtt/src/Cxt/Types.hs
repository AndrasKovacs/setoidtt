
module Cxt.Types where

import qualified Data.HashMap.Strict as M

import Common
import qualified Syntax as S
import qualified Values as V


data NameInfo =
    NITopDef Lvl V.Ty S.U
  | NIPostulate Lvl V.Ty S.U
  | NILocal Lvl V.Ty S.U

-- | Table of names used for scoping raw identifiers. Note: we have *more* names around
--   than these, as elaboration can invent names and insert binders. This table only
--   maps raw identifiers that are possibly referenced in source code.
type NameTable = M.HashMap RawName NameInfo -- TODO: better Eq + Hashable for ByteString

data Cxt = Cxt {
  _env       :: V.Env,
  _lvl       :: Lvl,
  _locals    :: S.Locals,
  _nameTable :: NameTable,
  _src       :: ~RawName
  }

instance Show Cxt where
  show cxt = show $ _locals cxt
