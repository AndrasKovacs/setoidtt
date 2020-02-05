
module Evaluation where

import Types
import ElabState

vProj1 :: Val -> Val
vProj1 (VTcons t u)    = t
vProj1 (VNe h sp)      = VNe h (SProj1 sp)
vProj1 (VLamTel x a t) = vProj1 (vLamTel id x a t)
vProj1 _               = error "impossible"

vProj2 :: Val -> Val
vProj2 (VTcons t u)    = u
vProj2 (VNe h sp)      = VNe h (SProj2 sp)
vProj2 (VLamTel x a t) = vProj2 (vLamTel id x a t)
vProj2 _               = error "impossible"

vVar :: Ix -> Vals -> Val
vVar 0 (VDef vs v) = v
vVar 0 (VSkip vs)  = VVar (valsLen vs)
vVar x (VDef vs _) = vVar (x - 1) vs
vVar x (VSkip vs)  = vVar (x - 1) vs
vVar _ _           = error "impossible"

vMeta :: MId -> Val
vMeta m = case lookupMeta m of
  Unsolved{} -> VMeta m
  Solved v   -> v
  _          -> error "impossible"

-- | Force the outermost constructor in a value, do not force the spine
--   of a neutral value.
force :: Val -> Val
force = \case
  v@(VNe (HMeta m) sp) -> case lookupMeta m of
    Unsolved{} -> v
    Solved v   -> force (vAppSp v sp)
    _          -> error "impossible"
  VPiTel x a b  -> vPiTel force x a b
  VLamTel x a t -> vLamTel force x a t
  v             -> v

-- | Force a spine, computing telescope applications where possible.
forceSp :: Spine -> Spine
forceSp sp =
  -- This a cheeky hack, the point is that (VVar (-1)) blocks computation, and
  -- we get back the new spine.  We use (-1) in order to make the hack clear in
  -- potential debugging situations.
  case vAppSp (VVar (-1)) sp of
    VNe _ sp -> sp
    _        -> error "impossible"

vApp :: Val -> Val -> Icit -> Val
vApp (VLam _ _ _ t)  ~u i = t u
vApp (VNe h sp)      ~u i = VNe h (SApp sp u i)
vApp (VLamTel x a t) ~u i = vApp (vLamTel id x a t) u i
vApp _                _ _ = error "impossible"

vPiTel :: (Val -> Val) -> Name -> VTy -> (Val -> Val) -> Val
vPiTel k x a b = case force a of
  VTEmpty        -> k (b VTempty)
  VTCons x1 a as -> let x1 = x ++ "1"
                        x2 = x ++ "2"
                    in VPi x1 Impl a $ \ ~x1 ->
                       vPiTel id x2 (as x1) $ \ ~x2 -> b (VTcons x1 x2)
  a -> VPiTel x a b

vLamTel :: (Val -> Val) -> Name -> VTy -> (Val -> Val) -> Val
vLamTel k x a t = case force a of
  VTEmpty       -> k (t VTEmpty)
  VTCons _ a as -> let x1 = x ++ "1"
                       x2 = x ++ "2"
                   in VLam x1 Impl a $ \ ~x1 ->
                      vLamTel id x2 (as x1) $ \ ~x2 -> t (VTcons x1 x2)
  a             -> VLamTel x a t

vAppTel ::  VTy -> Val -> Val -> Val
vAppTel a ~t ~u = case force a of
  VTEmpty       -> t
  VTCons _ a as -> let u1 = vProj1 u in vAppTel (as u1) (vApp t u1 Impl) (vProj2 u)
  a             -> case t of
                     VLamTel _ _ t -> t u
                     VNe h sp      -> VNe h (SAppTel a sp u)
                     _             -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp h = go where
  go SNil             = h
  go (SApp sp u i)    = vApp (go sp) u i
  go (SAppTel a sp u) = vAppTel a (go sp) u
  go (SProj1 sp)      = vProj1 (go sp)
  go (SProj2 sp)      = vProj2 (go sp)

eval :: Vals -> Tm -> Val
eval vs = \case
  Var x        -> vVar x vs
  Let x _ t u  -> eval (VDef vs (eval vs t)) u
  U            -> VU
  Meta m       -> vMeta m
  Pi x i a b   -> VPi x i (eval vs a) $ \x -> eval (VDef vs x) b
  Lam x i a t  -> VLam x i (eval vs a) $ \x -> eval (VDef vs x) t
  App t u i    -> vApp (eval vs t) (eval vs u) i
  Tel          -> VTel
  TEmpty       -> VTEmpty
  TCons x a b  -> VTCons x (eval vs a) $ \x -> eval (VDef vs x) b
  Rec a        -> VRec (eval vs a)
  Tempty       -> VTempty
  Tcons t u    -> VTcons (eval vs t) (eval vs u)
  Proj1 t      -> vProj1 (eval vs t)
  Proj2 t      -> vProj2 (eval vs t)
  PiTel x a b  -> vPiTel id x (eval vs a) $ \x -> eval (VDef vs x) b
  AppTel a t u -> vAppTel (eval vs a) (eval vs t) (eval vs u)
  LamTel x a t -> vLamTel id x (eval vs a) $ \x -> eval (VDef vs x) t

quote :: Lvl -> Val -> Tm
quote d v = case force v of
  VNe h sp ->
    let go SNil = case h of
          HMeta m -> Meta m
          HVar x  -> Var x
        go (SApp sp u i)    = App (go sp) (quote d u) i
        go (SAppTel a sp u) = AppTel (quote d a) (go sp) (quote d u)
        go (SProj1 sp)      = Proj1 (go sp)
        go (SProj2 sp)      = Proj2 (go sp)
    in go (forceSp sp)

  VLam x i a t  -> Lam x i (quote d a) (quote (d + 1) (t (VVar d)))
  VPi x i a b   -> Pi x i (quote d a) (quote (d + 1) (b (VVar d)))
  VU            -> U
  VTel          -> Tel
  VRec a        -> Rec (quote d a)
  VTEmpty       -> TEmpty
  VTCons x a as -> TCons x (quote d a) (quote (d + 1) (as (VVar d)))
  VTempty       -> Tempty
  VTcons t u    -> Tcons (quote d t) (quote d u)
  VPiTel x a b  -> PiTel x (quote d a) (quote (d + 1) (b (VVar d)))
  VLamTel x a t -> LamTel x (quote d a) (quote (d + 1) (t (VVar d)))

nf :: Vals -> Tm -> Tm
nf vs t = quote (valsLen vs) (eval vs t)

-- zonking
--------------------------------------------------------------------------------

zonkSp :: Vals -> Tm -> Either Val Tm
zonkSp vs = \case
  Meta m       -> case lookupMeta m of
                    Solved v -> Left v
                    _        -> Right (Meta m)
  App t u ni   -> case zonkSp vs t of
                    Left t  -> Left (vApp t (eval vs u) ni)
                    Right t -> Right $ App t (zonk vs u) ni
  AppTel a t u -> case zonkSp vs t of
                    Left t  -> Left (vAppTel (eval vs a) t (eval vs u))
                    Right t -> Right $ AppTel (zonk vs a) t (zonk vs u)
  t            -> Right (zonk vs t)

zonk :: Vals -> Tm -> Tm
zonk vs = \case
  Var x        -> Var x
  Meta m       -> case lookupMeta m of
                    Solved v   -> quote (valsLen vs) v
                    Unsolved{} -> Meta m
                    _          -> error "impossible"
  U            -> U
  Pi x i a b   -> Pi x i (zonk vs a) (zonk (VSkip vs) b)
  App t u ni   -> case zonkSp vs t of
                    Left t  -> quote (valsLen vs) (vApp t (eval vs u) ni)
                    Right t -> App t (zonk vs u) ni
  Lam x i a t  -> Lam x i (zonk vs a) (zonk (VSkip vs) t)
  Let x a t u  -> Let x (zonk vs a) (zonk vs t) (zonk (VSkip vs) u)
  Tel          -> Tel
  TEmpty       -> TEmpty
  TCons x t u  -> TCons x (zonk vs t) (zonk (VSkip vs) u)
  Rec a        -> Rec (zonk vs a)
  Tempty       -> Tempty
  Tcons t u    -> Tcons (zonk vs t) (zonk vs u)
  Proj1 t      -> Proj1 (zonk vs t)
  Proj2 t      -> Proj2 (zonk vs t)
  PiTel x a b  -> PiTel x (zonk vs a) (zonk (VSkip vs) b)
  AppTel a t u -> case zonkSp vs t of
                    Left t  -> quote (valsLen vs) (vAppTel (eval vs a) t (eval vs u))
                    Right t -> AppTel (zonk vs a) t (zonk vs u)
  LamTel x a b -> LamTel x (zonk vs a) (zonk (VSkip vs) b)
