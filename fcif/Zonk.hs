
module Zonk where

import Types
import Evaluation
import ElabState

-- | Unfold all metas and evaluate meta-headed spines, but don't evaluate
--   anything else.
zonk :: Vals -> Tm -> Tm
zonk vs t = go t where

  goSp :: Tm -> Either Val Tm
  goSp = \case
    Meta m        -> case runLookupMeta m of
                       Solved v -> Left v
                       _        -> Right (Meta m)
    App t u un ni -> case goSp t of
                       Left t  -> Left (vApp t (eval vs u) (eval vs un) ni)
                       Right t -> Right $ App t (go u) (go un) ni
    t             -> Right (zonk vs t)

  goBind = zonk (VSkip vs)

  go = \case
    Var x          -> Var x
    Meta m         -> case runLookupMeta m of
                        Solved v   -> quote (valsLen vs) v
                        Unsolved{} -> Meta m
    Set            -> Set
    Prop           -> Prop
    Pi x i a un b  -> Pi x i (go a) (go un) (goBind b)
    App t u un ni  -> case goSp t of
                        Left t  -> quote (valsLen vs) (vApp t (eval vs u) (eval vs un) ni)
                        Right t -> App t (go u) (go un) ni
    Lam x i a un t -> Lam x i (go a) (go un) (goBind t)
    Let x a un t u -> Let x (go a) (go un) (go t) (goBind u)
    Skip t         -> Skip (goBind t)
