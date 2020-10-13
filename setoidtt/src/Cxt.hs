
module Cxt where

import qualified Data.HashMap.Strict as M

import qualified Syntax as S
import qualified Value  as V

import Eval
import Common

data NameInfo =
    NITopDef Lvl ~V.WTy S.U
  | NIPostulate Lvl ~V.WTy S.U
  | NILocal Lvl ~V.WTy S.U

-- | Table of names used for scoping raw identifiers. Note: we have *more* names around
--   than these, as elaboration can invent names and insert binders. This table only
--   maps raw identifiers that are possibly referenced in source code.
type NameTable = M.HashMap RawName NameInfo -- TODO: better Eq + Hashable for ByteString

data Locals
  = LEmpty
  | LDefine Locals Name S.Tm S.Ty S.U
  | LBind Locals Name S.Ty S.U

data Cxt = Cxt {
  _env       :: V.Env,
  _lvl       :: Lvl,
  _locals    :: Locals,
  _nameTable :: NameTable,
  _src       :: RawName
  }

emptyCxt :: RawName -> Cxt
emptyCxt = Cxt LNil 0 LEmpty mempty
{-# noinline emptyCxt #-}

bind :: RawName -> S.Ty -> S.U -> Cxt -> Cxt
bind x a au cxt@(Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (LBind loc (NName x) a au)
      (M.insert x (NILocal l (unS (eval env l a)) au) ntbl)
      src
{-# inline bind #-}

insert :: RawName -> S.Ty -> S.U -> Cxt -> Cxt
insert x a au cxt@(Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (LBind loc (NName x) a au)
      ntbl
      src
{-# inline insert #-}

define :: RawName -> S.Tm -> S.Ty -> S.U -> Cxt -> Cxt
define x t a au (Cxt env l loc ntbl src) =
  Cxt (LSnoc env (unS (eval env l t)))
      (l + 1)
      (LDefine loc (NName x) t a au)
      (M.insert x (NILocal l (unS (eval env l a)) au) ntbl)
      src
{-# inline define #-}

define' :: RawName -> S.Tm -> S.Ty -> V.Ty -> S.U -> Cxt -> Cxt
define' x t a va au (Cxt env l loc ntbl src) =
  Cxt (LSnoc env (unS (eval env l t)))
      (l + 1)
      (LDefine loc (NName x) t a au)
      (M.insert x (NILocal l (unS va) au) ntbl)
      src
{-# inline define' #-}

liftVal :: Cxt -> V.Val -> (V.Val -> V.Val)
liftVal cxt t ~u =
  let env = LSnoc (_env cxt) (unS u)
      l   = _lvl cxt + 1
  in eval env l (quote l DontUnfold t)
{-# inline liftVal #-}
