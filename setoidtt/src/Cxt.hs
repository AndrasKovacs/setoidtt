
module Cxt where

import qualified Data.HashMap.Strict as M

import qualified Syntax as S
import qualified Values as V

import Evaluation
import Common

data NameInfo =
    NITopDef Lvl ~V.WTy S.U
  | NIPostulate Lvl ~V.WTy S.U
  | NILocal Lvl ~V.WTy S.U

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

emptyCxt :: RawName -> Cxt
emptyCxt = Cxt V.Nil 0 S.Empty mempty
{-# noinline emptyCxt #-}

bind :: RawName -> S.Ty -> S.U -> Cxt -> Cxt
bind x a au cxt@(Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (S.Bind loc (NName x) a au)
      (M.insert x (NILocal l (unS (eval env l a)) au) ntbl)
      src
{-# inline bind #-}

bindEmpty :: S.Ty -> S.U -> Cxt -> Cxt
bindEmpty a au cxt@(Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (S.Bind loc NEmpty a au)
      ntbl
      src
{-# inline bindEmpty #-}

bind' :: RawName -> S.Ty -> V.Ty -> S.U -> Cxt -> Cxt
bind' x a va au cxt@(Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (S.Bind loc (NName x) a au)
      (M.insert x (NILocal l (unS va) au) ntbl)
      src
{-# inline bind' #-}

bindEmpty' :: S.Ty -> V.Ty -> S.U -> Cxt -> Cxt
bindEmpty' a va au cxt@(Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (S.Bind loc NEmpty a au)
      ntbl
      src
{-# inline bindEmpty' #-}

newBinder :: Name -> S.Ty -> S.U -> Cxt -> Cxt
newBinder x a au cxt@(Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (S.Bind loc x a au)
      ntbl
      src
{-# inline newBinder #-}

define :: RawName -> S.Tm -> S.Ty -> S.U -> Cxt -> Cxt
define x t a au (Cxt env l loc ntbl src) =
  Cxt (V.Snoc env (unS (eval env l t)))
      (l + 1)
      (S.Define loc (NName x) t a au)
      (M.insert x (NILocal l (unS (eval env l a)) au) ntbl)
      src
{-# inline define #-}

define' :: RawName -> S.Tm -> V.Val -> S.Ty -> V.Ty -> S.U -> Cxt -> Cxt
define' x t vt a va au (Cxt env l loc ntbl src) =
  Cxt (V.Snoc env (unS vt))
      (l + 1)
      (S.Define loc (NName x) t a au)
      (M.insert x (NILocal l (unS va) au) ntbl)
      src
{-# inline define' #-}

closeVal :: Cxt -> V.Val -> V.Closure
closeVal cxt t =
  V.Close (_env cxt) (_lvl cxt) (quote (_lvl cxt + 1) DontUnfold t)
{-# inline closeVal #-}
