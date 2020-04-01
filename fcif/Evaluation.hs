
module Evaluation where

import qualified Data.IntSet as IS

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
  UMax as -> IS.foldl' (\u x -> u <> maybe (UMeta x) forceU (runLookupU x)) Prop as
  u       -> u

vApp :: Val -> Val -> U -> Icit -> Val
vApp (VLam _ _ _ _ t) ~u un i = t u
vApp (VNe h sp)       ~u un i = VNe h (SApp sp u un i)
vApp _                _  un _ = error "impossible"

vProj1 :: Val -> U -> Val
vProj1 v vu = case v of
  VPair t _ u _ -> t
  VNe h sp      -> VNe h (SProj1 sp vu)
  _             -> error "impossible"

vProj2 :: Val -> U -> Val
vProj2 v vu = case v of
  VPair t _ u _ -> u
  VNe h sp      -> VNe h (SProj2 sp vu)
  _             -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp h = go where
  go SNil             = h
  go (SApp sp u uu i) = vApp (go sp) u uu i
  go (SProj1 sp spu)  = vProj1 (go sp) spu
  go (SProj2 sp spu)  = vProj2 (go sp) spu

vAppSI ~t ~u = vApp t u Set  Impl
vAppSE ~t ~u = vApp t u Set  Expl
vAppPI ~t ~u = vApp t u Prop Impl
vAppPE ~t ~u = vApp t u Prop Expl

vExfalso u a t   = vApp (VAxiom (AExfalso u) `vAppSI` a) t u Expl
vRfl     a t     = VAxiom ARfl `vAppSI`  a `vAppSI`  t
vSym a x y p     = VAxiom ASym `vAppSI`  a `vAppSI`  x `vAppSI`  y `vAppPE`  p
vAp  a b f x y p = VAxiom AAp  `vAppSI`  a `vAppSI`  b `vAppSE`  f `vAppSI`  x `vAppSI`  y
                               `vAppPE`  p

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
    Eq             -> VLamIS "A" VSet \ ~a -> VLamES "x" a \ ~x -> VLamES "y" a \ ~y ->
                      VEq a x y
    Coe u          -> VLamIS "A" (VU u) \ ~a -> VLamIS "B" (VU u) \ ~b ->
                      VLamEP "p" (VEq (VU u) a b) \ ~p -> VLam "t" Expl a u \ ~t ->
                      VNe (HCoe u a b p t) SNil
    Exfalso u      -> VLamIS "A" (VU u) \ ~a -> VLamEP "p" VBot \ ~t ->
                      vExfalso u a t
    Rfl            -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x -> vRfl a x
    Sym            -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamEP "p" (VEq a x y) \ ~p ->
                      vSym a x y p
    Ap             -> VLamIS "A" VSet \ ~a -> VLamIS "B" VSet \ ~b ->
                      VLamES "f" (VPiES "_" a (const b)) \ ~f -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamEP "p" (VEq a x y) \ ~p ->
                      vAp a b f x y p

    Sg x a au b bu -> VSg x (go a) au (goBind b) bu
    Pair t tu u uu -> VPair (go t) tu (go u) uu
    Proj1 t tu     -> vProj1 (go t) tu
    Proj2 t tu     -> vProj2 (go t) tu

  goBind t v = eval (VDef vs v) t

quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case force v of
    VNe h sp ->
      let goSp SNil = case h of
            HMeta m        -> Meta m
            HVar x         -> Var (d - x - 1)
            HCoe u a b p t -> tCoe u (go a) (go b) (go p) (go t)
            HAxiom ax      -> case ax of
              ARfl       -> Rfl
              ASym       -> Sym
              AAp        -> Ap
              AExfalso u -> Exfalso u

          goSp (SApp sp u uu i) = App (goSp sp) (go u) uu i
          goSp (SProj1 sp spu)  = Proj1 (goSp sp) spu
          goSp (SProj2 sp spu)  = Proj2 (goSp sp) spu

      in goSp sp

    VLam x i a au t -> Lam x i (go a) au (goBind t)
    VPi x i a au b  -> Pi x i (go a) au (goBind b)
    VU u            -> U (forceU u)
    VTop            -> Top
    VTt             -> Tt
    VBot            -> Bot
    VEq a t u       -> tEq (go a) (go t) (go u)

    VSg x a au b bu -> Sg x (go a) au (goBind b) bu
    VPair t tu u uu -> Pair (go t) tu (go u) uu

  goBind t = quote (d + 1) (t (VVar d))
