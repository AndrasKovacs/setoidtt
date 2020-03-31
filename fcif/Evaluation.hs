
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
    Nothing -> u
    Just u  -> forceU u
  u           -> u

vApp :: Val -> Val -> U -> Icit -> Val
vApp (VLam _ _ _ _ t) ~u un i = t u
vApp (VNe h sp)       ~u un i = VNe h (SApp sp u un i)
vApp _                _  un _ = error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp h = go where
  go SNil             = h
  go (SApp sp u uu i) = vApp (go sp) u uu i

-- vEq :: Val -> Val -> Val -> Val
-- vEq a t u = case a of
--   VSet -> case (t, u) of

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
    Top            -> VTop
    Tt             -> VTt
    Bot            -> VBot
    Exfalso u      -> VLamIS "A" (VU u) \ ~a -> VLamEP "p" VBot \ ~t ->
                      VExfalso u a t
    Eq             -> VLamIS "A" VSet \ ~a -> VLamES "x" a \ ~x -> VLamES "y" a \ ~y ->
                      VEq a x y
    Rfl            -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x -> VRfl a x
    Coe u          -> VLamIS "A" (VU u) \ ~a -> VLamIS "B" (VU u) \ ~b ->
                      VLamEP "p" (VEq (VU u) a b) \ ~p -> VLam "t" Expl a u \ ~t ->
                      VCoe u a b p t
    Sym            -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamEP "p" (VEq a x y) \ ~p ->
                      VSym a x y p
    Ap             -> VLamIS "A" VSet \ ~a -> VLamIS "B" VSet \ ~b ->
                      VLamES "f" (vFunES a b) \ ~f -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamEP "p" (VEq a x y) \ ~p ->
                      VAp a b f x y p
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
    VTop            -> Top
    VTt             -> Tt
    VBot            -> Bot
    VExfalso u a t  -> Exfalso' u (go a) (go t)
    VEq a t u       -> Eq' (go a) (go t) (go u)
    VRfl a t        -> Rfl' (go a) (go t)
    VCoe u a b p t  -> Coe' u (go a) (go b) (go p) (go t)
    VSym a x y p    -> Sym' (go a) (go x) (go y) (go p)
    VAp a b f x y p -> Ap' (go a) (go b) (go f) (go x) (go y) (go p)

  goBind t = quote (d + 1) (t (VVar d))
