
module Cxt where

import qualified Data.HashMap.Strict as M
import qualified Data.ByteString as B

import qualified LvlSet as LS
import qualified Syntax as S
import qualified Value  as V
import Eval
import Common

data Types = TyNil | TySnoc Types Name ~V.Ty ~S.U
data NameInfo = NameInfo Lvl ~V.Ty ~S.U


-- | Table of names used for scoping raw identifiers. Note: we have *more* names around
--   than these, as elaboration can invent names and insert binders. This table only
--   maps raw identifiers that are possibly referenced in source code.
type NameTable = M.HashMap B.ByteString NameInfo -- TODO: better Eq + Hashable for ByteString

data Cxt = Cxt {
  _env       :: V.Env,
  _lvl       :: Lvl,
  _types     :: Types,

  -- | Mask picking out the bound variables from local scope. Used to optimize fresh meta creation and evaluation:
  --   instead of applying a meta to all bound vars, we just store this mask. When we evaluate the fresh meta,
  --   we
  _boundVars :: LS.LvlSet,
  _nameTable :: NameTable
  }

emptyCxt :: Cxt
emptyCxt = Cxt V.Nil 0 TyNil mempty mempty
{-# noinline emptyCxt #-}

bind :: B.ByteString -> V.Ty -> S.U -> Cxt -> Cxt
bind x ~a ~au (Cxt env l as bound ns) =
  Cxt (V.Skip env l)
      (l + 1)
      (TySnoc as (NName x) a au)
      (LS.insert l bound)
      (M.insert x (NameInfo l a au) ns)

insert :: Name -> V.Ty -> S.U -> Cxt -> Cxt
insert x ~a ~au (Cxt env l as bound ns) =
  Cxt (V.Skip env l)
      (l + 1)
      (TySnoc as x a au)
      (LS.insert l bound)
      ns

define :: B.ByteString -> V.Val -> V.Ty -> S.U -> Cxt -> Cxt
define x ~t ~a ~au (Cxt env l as bound ns) =
  Cxt (V.Snoc env t)
      (l + 1)
      (TySnoc as (NName x) a au)
      bound
      (M.insert x (NameInfo l a au) ns)

-- liftVal :: Cxt -> V.Val -> (V.Val -> V.Val)
-- liftVal cxt t ~u = eval _ _ _
