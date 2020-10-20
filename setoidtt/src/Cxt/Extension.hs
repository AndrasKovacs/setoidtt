
module Cxt.Extension where

import qualified Data.HashMap.Strict as M

import Common
import Cxt.Types
import Evaluation

import qualified Syntax as S
import qualified Values as V

--------------------------------------------------------------------------------

emptyCxt :: RawName -> Cxt
emptyCxt = Cxt V.Nil 0 S.Empty mempty
{-# inline emptyCxt #-}

bind :: RawName -> S.Ty -> S.U -> Cxt -> Cxt
bind x a au (Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (S.Bind loc (NName x) a au)
      (M.insert x (NILocal l (eval env l a) au) ntbl)
      src
{-# inline bind #-}

bindEmpty :: S.Ty -> S.U -> Cxt -> Cxt
bindEmpty a au (Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (S.Bind loc NEmpty a au)
      ntbl
      src
{-# inline bindEmpty #-}

bind' :: RawName -> S.Ty -> V.Ty -> S.U -> Cxt -> Cxt
bind' x a va au (Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (S.Bind loc (NName x) a au)
      (M.insert x (NILocal l va au) ntbl)
      src
{-# inline bind' #-}

bindEmpty' :: S.Ty -> V.Ty -> S.U -> Cxt -> Cxt
bindEmpty' a va au (Cxt env l loc ntbl src) =
  Cxt (V.Skip env l)
      (l + 1)
      (S.Bind loc NEmpty a au)
      ntbl
      src
{-# inline bindEmpty' #-}

newBinder :: Name -> S.Ty -> S.U -> Cxt -> Cxt
newBinder x a au (Cxt env l loc ntbl src) =
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
      (M.insert x (NILocal l (eval env l a) au) ntbl)
      src
{-# inline define #-}

define' :: RawName -> S.Tm -> V.WVal -> S.Ty -> V.Ty -> S.U -> Cxt -> Cxt
define' x t ~vt a va au (Cxt env l loc ntbl src) =
  Cxt (V.Snoc env vt)
      (l + 1)
      (S.Define loc (NName x) t a au)
      (M.insert x (NILocal l va au) ntbl)
      src
{-# inline define' #-}

closeVal :: Cxt -> V.Val -> V.Closure
closeVal cxt t =
  V.Close (_env cxt) (_lvl cxt) (quote (_lvl cxt + 1) DontUnfold t)
{-# inline closeVal #-}
