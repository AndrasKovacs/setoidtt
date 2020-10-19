
module EvalCxt (
    eval, forceF, forceFU, forceFUE, quote, vEq
  , (Eval.$$), (Eval.$$$), Eval.vApp, Eval.vAppSE
  , Eval.vProj1, Eval.vProj2, Eval.vProjField) where

import Common
import Cxt
import Syntax
import Values

import qualified Evaluation as Eval

eval :: Cxt -> Tm -> Val
eval cxt t = Eval.eval (_env cxt) (_lvl cxt) t
{-# inline eval #-}

forceF :: Cxt -> Val -> Val
forceF cxt t = Eval.forceF (_lvl cxt) t
{-# inline forceF #-}

forceFU :: Cxt -> Val -> Val
forceFU cxt t = Eval.forceFU (_lvl cxt) t
{-# inline forceFU #-}

forceFUE :: Cxt -> Val -> Val
forceFUE cxt t = Eval.forceFUE (_lvl cxt) t
{-# inline forceFUE #-}

quote :: Cxt -> Unfolding -> Val -> Tm
quote cxt unf t = Eval.quote (_lvl cxt) unf t
{-# inline quote #-}

vEq :: Cxt -> Val -> Val -> Val -> Val
vEq cxt a t u = Eval.vEq (_lvl cxt) a t u
{-# inline vEq #-}
