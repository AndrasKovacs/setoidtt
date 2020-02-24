
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
    Meta m       -> case runLookupMeta m of
                      Solved v -> Left v
                      _        -> Right (Meta m)
    App t u ni   -> case goSp t of
                      Left t  -> Left (vApp t (eval vs u) ni)
                      Right t -> Right $ App t (go u) ni
    AppTel a t u -> case goSp t of
                      Left t  -> Left (vAppTel (eval vs a) t (eval vs u))
                      Right t -> Right $ AppTel (go a) t (go u)
    t            -> Right (zonk vs t)

  goBind = zonk (VSkip vs)

  go = \case
    Var x        -> Var x
    Meta m       -> case runLookupMeta m of
                      Solved v   -> quote (valsLen vs) v
                      Unsolved{} -> Meta m
                      _          -> error "impossible"
    U            -> U
    Pi x i a b   -> Pi x i (go a) (goBind b)
    App t u ni   -> case goSp t of
                      Left t  -> quote (valsLen vs) (vApp t (eval vs u) ni)
                      Right t -> App t (go u) ni
    Lam x i a t  -> Lam x i (go a) (goBind t)
    Let x a t u  -> Let x (go a) (go t) (goBind u)
    Tel          -> Tel
    TEmpty       -> TEmpty
    TCons x t u  -> TCons x (go t) (goBind u)
    Rec a        -> Rec (go a)
    Tempty       -> Tempty
    Tcons t u    -> Tcons (go t) (go u)
    Proj1 t      -> Proj1 (go t)
    Proj2 t      -> Proj2 (go t)
    PiTel x a b  -> PiTel x (go a) (goBind b)
    AppTel a t u -> case goSp t of
                      Left t  -> quote (valsLen vs) (vAppTel (eval vs a) t (eval vs u))
                      Right t -> AppTel (go a) t (go u)
    LamTel x a b -> LamTel x (go a) (goBind b)
    Skip t       -> Skip (goBind t)
