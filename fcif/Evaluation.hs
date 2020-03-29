
module Evaluation where

import Types
import ElabState

vVar :: Ix -> Vals -> Val
vVar 0 (VDef vs v) = v
vVar 0 (VSkip vs)  = VVar (valsLen vs)
vVar x (VDef vs _) = vVar (x - 1) vs
vVar x (VSkip vs)  = vVar (x - 1) vs
vVar _ _           = error "impossible"

vMeta :: MId -> Val
vMeta m = case runLookupMeta m of
  Unsolved{} -> VMeta m
  Solved v   -> v

-- | Force the outermost constructor in a value.
force :: Val -> Val
force = \case
  v@(VNe (HMeta m) sp) -> case runLookupMeta m of
    Unsolved{} -> v
    Solved v   -> force (vAppSp v sp)
  v            -> v

forceU :: U -> U
forceU = \case
  u@(UMeta m) -> case runLookupU m of
    Just u  -> u
    Nothing -> u
  u           -> u

vApp :: Val -> Val -> U -> Icit -> Val
vApp (VLam _ _ _ _ t) ~u un i = t u
vApp (VNe h sp)       ~u un i = VNe h (SApp sp u un i)
vApp _                _  un _  = error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp h = go where
  go SNil             = h
  go (SApp sp u uu i) = vApp (go sp) u uu i

eval :: Vals -> Tm -> Val
eval vs = go where
  go = \case
    Var x          -> vVar x vs
    Let x a au t u -> goBind u (go t)
    Meta m         -> vMeta m
    Pi x i a au b  -> VPi x i (go a) au (goBind b)
    Lam x i a au t -> VLam x i (go a) au (goBind t)
    App t u uu i   -> vApp (go t) (go u) uu i
    Skip t         -> eval (VSkip vs) t
    U u            -> VU u

  goBind t v = eval (VDef vs v) t

quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case force v of
    VNe h sp ->
      let goSp SNil = case h of
            HMeta m -> Meta m
            HVar x  -> Var (d - x - 1)
          goSp (SApp sp u uu i) = App (goSp sp) (go u) uu i
      in goSp sp

    VLam x i a au t -> Lam x i (go a) au (goBind t)
    VPi x i a au b  -> Pi x i (go a) au (goBind b)
    VU u            -> U (forceU u)

  goBind t = quote (d + 1) (t (VVar d))
