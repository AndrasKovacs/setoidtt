
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

-- | Force the outermost constructor in a value, do not force the spine
--   of a neutral value.
force :: Val -> Val
force = \case
  v@(VNe (HMeta m) sp) -> case runLookupMeta m of
    Unsolved{} -> v
    Solved v   -> force (vAppSp v sp)
  v            -> v

-- | Force a spine, computing telescope applications where possible.
forceSp :: Spine -> Spine
forceSp sp =
  -- This is a cheeky hack, the point is that (VVar (-1)) blocks computation, and
  -- we get back the new spine.  We use (-1) in order to make the hack clear in
  -- potential debugging situations.
  case vAppSp (VVar (-1)) sp of
    VNe _ sp -> sp
    _        -> error "impossible"

vApp :: Val -> Val -> VUniv -> Icit -> Val
vApp (VLam _ _ _ _ t) ~un ~u i = t u
vApp (VNe h sp)       ~un ~u i = VNe h (SApp sp u un i)
vApp _                ~un _ _  = error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp h = go where
  go SNil             = h
  go (SApp sp u un i) = vApp (go sp) u un i

eval :: Vals -> Tm -> Val
eval vs = go where
  go = \case
    Var x          -> vVar x vs
    Let x _ _ t u  -> goBind u (go t)
    Set            -> VSet
    Prop           -> VProp
    Meta m         -> vMeta m
    Pi x i a un b  -> VPi x i (go a) (go un) (goBind b)
    Lam x i a un t -> VLam x i (go a) (go un) (goBind t)
    App t u un i   -> vApp (go t) (go u) (go un) i
    Skip t         -> eval (VSkip vs) t

  goBind t x = eval (VDef vs x) t


quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case force v of
    VNe h sp ->
      let goSp SNil = case h of
            HMeta m -> Meta m
            HVar x  -> Var (d - x - 1)
          goSp (SApp sp u un i) = App (goSp sp) (go u) (go un) i
      in goSp (forceSp sp)

    VLam x i a un t -> Lam x i (go a) (go un) (goBind t)
    VPi x i a un b  -> Pi x i (go a) (go un) (goBind b)
    VSet            -> Set
    VProp           -> Prop

  goBind t = quote (d + 1) (t (VVar d))
