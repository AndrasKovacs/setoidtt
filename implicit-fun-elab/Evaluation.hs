
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
vMeta m = case runLookupMeta m of
  Unsolved{} -> VMeta m
  Solved v   -> v
  _          -> error "impossible"

-- | Force the outermost constructor in a value, do not force the spine
--   of a neutral value.
force :: Val -> Val
force = \case
  v@(VNe (HMeta m) sp) -> case runLookupMeta m of
    Unsolved{} -> v
    Solved v   -> force (vAppSp v sp)
    _          -> error "impossible"
  VPiTel x a b  -> vPiTel force x a b
  VLamTel x a t -> vLamTel force x a t
  v             -> v

-- | Force a spine, computing telescope applications where possible.
forceSp :: Spine -> Spine
forceSp sp =
  -- This is a cheeky hack, the point is that (VVar (-1)) blocks computation, and
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
  a              -> VPiTel x a b

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
                     VNe h sp      -> VNe h (SAppTel a sp u)
                     VLamTel _ _ t -> t u
                     _             -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp h = go where
  go SNil             = h
  go (SApp sp u i)    = vApp (go sp) u i
  go (SAppTel a sp u) = vAppTel a (go sp) u
  go (SProj1 sp)      = vProj1 (go sp)
  go (SProj2 sp)      = vProj2 (go sp)

eval :: Vals -> Tm -> Val
eval vs = go where
  go = \case
    Var x        -> vVar x vs
    Let x _ t u  -> goBind u (go t)
    U            -> VU
    Meta m       -> vMeta m
    Pi x i a b   -> VPi x i (go a) (goBind b)
    Lam x i a t  -> VLam x i (go a) (goBind t)
    App t u i    -> vApp (go t) (go u) i
    Tel          -> VTel
    TEmpty       -> VTEmpty
    TCons x a b  -> VTCons x (go a) (goBind b)
    Rec a        -> VRec (go a)
    Tempty       -> VTempty
    Tcons t u    -> VTcons (go t) (go u)
    Proj1 t      -> vProj1 (go t)
    Proj2 t      -> vProj2 (go t)
    PiTel x a b  -> vPiTel id x (go a) (goBind b)
    AppTel a t u -> vAppTel (go a) (go t) (go u)
    LamTel x a t -> vLamTel id x (go a) (goBind t)
    Skip t       -> eval (VSkip vs) t

  goBind t x = eval (VDef vs x) t


quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case force v of
    VNe h sp ->
      let goSp SNil = case h of
            HMeta m -> Meta m
            HVar x  -> Var (d - x - 1)
          goSp (SApp sp u i)    = App (goSp sp) (go u) i
          goSp (SAppTel a sp u) = AppTel (go a) (goSp sp) (go u)
          goSp (SProj1 sp)      = Proj1 (goSp sp)
          goSp (SProj2 sp)      = Proj2 (goSp sp)
      in goSp (forceSp sp)

    VLam x i a t  -> Lam x i (go a) (goBind t)
    VPi x i a b   -> Pi x i (go a) (goBind b)
    VU            -> U
    VTel          -> Tel
    VRec a        -> Rec (go a)
    VTEmpty       -> TEmpty
    VTCons x a as -> TCons x (go a) (goBind as)
    VTempty       -> Tempty
    VTcons t u    -> Tcons (go t) (go u)
    VPiTel x a b  -> PiTel x (go a) (goBind b)
    VLamTel x a t -> LamTel x (go a) (goBind t)

  goBind t = quote (d + 1) (t (VVar d))


-- zonking
--------------------------------------------------------------------------------

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
