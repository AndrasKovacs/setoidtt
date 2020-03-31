
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
    App t u uu ni -> case goSp t of
                       Left t  -> Left (vApp t (eval vs u) (forceU uu) ni)
                       Right t -> Right $ App t (go u) (forceU uu) ni
    t             -> Right (zonk vs t)

  goBind = zonk (VSkip vs)

  go = \case
    Var x          -> Var x
    Meta m         -> case runLookupMeta m of
                        Solved v   -> quote (valsLen vs) v
                        Unsolved{} -> Meta m
    U u            -> U (forceU u)
    Pi x i a au b  -> Pi x i (go a) (forceU au) (goBind b)
    App t u uu ni  -> case goSp t of
                        Left t  -> quote (valsLen vs) (vApp t (eval vs u) (forceU uu) ni)
                        Right t -> App t (go u) (forceU uu) ni
    Lam x i a au t -> Lam x i (go a) (forceU au) (goBind t)
    Let x a au t u -> Let x (go a) (forceU au) (go t) (goBind u)
    Skip t         -> Skip (goBind t)
    Top            -> Top
    Tt             -> Tt
    Bot            -> Bot
    Exfalso u      -> Exfalso u
    Eq             -> Eq
    Rfl            -> Rfl
    Coe u          -> Coe u
    Sym            -> Sym
    Ap             -> Ap
