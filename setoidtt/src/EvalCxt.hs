
module EvalCxt (eval, force, quote, vEq, (Eval.$$), (Eval.$$$)) where

import Common
import Cxt
import Syntax
import Values

import qualified Evaluation as Eval

eval :: Cxt -> Tm -> Val
eval cxt t = Eval.eval (_env cxt) (_lvl cxt) t
{-# inline eval #-}

force :: Cxt -> Val -> Val
force cxt t = Eval.force (_lvl cxt) t
{-# inline force #-}

quote :: Cxt -> Unfolding -> Val -> Tm
quote cxt unf t = Eval.quote (_lvl cxt) unf t
{-# inline quote #-}

vEq :: Cxt -> Val -> Val -> Val -> Val
vEq cxt a t u = Eval.vEq (_lvl cxt) a t u
{-# inline vEq #-}
