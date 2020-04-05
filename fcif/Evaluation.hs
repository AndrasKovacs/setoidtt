
module Evaluation where

import Control.Exception
import Control.Monad
import qualified Data.IntSet as IS

import Types
import ElabState

-- Evaluation
--------------------------------------------------------------------------------

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
force :: Lvl -> Val -> Val
force l = \case
  VNe h sp -> case h of
    HMeta m -> case runLookupMeta m of
      Unsolved{} -> VNe h sp
      Solved v   -> force l (vAppSp v sp)
    HCoe u a b p t ->
      vAppSp (vCoe l (forceU u) (force l a) (force l b) (force l p) (force l t)) sp
    _ -> VNe h sp

  VEq a x y    -> vEq l (force l a) (force l x) (force l y)
  VU u         -> VU (forceU u)
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

vExfalso u a t     = vApp (VAxiom (AExfalso u) `vAppSI` a) t u Expl
vRfl     a t       = VAxiom ARfl `vAppSI`  a `vAppSI`  t
vSym a x y p       = VAxiom ASym `vAppSI`  a `vAppSI`  x `vAppSI`  y `vAppPE`  p
vTrans a x y z p q = VAxiom ATrans `vAppSI`  a `vAppSI`  x `vAppSI`  y `vAppSI` z `vAppPE` p
                                   `vAppPE` q
vAp  a b f x y p   = VAxiom AAp  `vAppSI`  a `vAppSI`  b `vAppSE`  f `vAppSI`  x `vAppSI`  y
                                 `vAppPE`  p
vAnd :: Val -> Val -> Val
vAnd a b = VSg "_" a Prop (const b) Prop

vImpl :: Val -> Val -> Val
vImpl a b = VPi "_" Expl a Prop (const b)

vAll :: Name -> Val -> (Val -> Val) -> Val
vAll x a b = VPi x Expl a Prop b

vEx :: Name -> Val -> (Val -> Val) -> Val
vEx x a b = VSg x a Prop b Prop

(∙) :: Val -> Val -> Val
(∙) t u = vApp t u Set Expl
infixl 8 ∙

(∘) :: Val -> Val -> Val
(∘) t u = vApp t u Prop Expl
infixl 8 ∘

(■) :: Val -> Val -> Val
(■) t u = vApp t u Set Impl
infixl 8 ■

(□) :: Val -> Val -> Val
(□) t u = vApp t u Prop Impl
infixl 8 □

vEq :: Lvl -> Val -> Val -> Val -> Val
vEq l topA ~topX ~topY = case topA of

  VU Prop ->
    vAnd (vImpl topX topY) (vImpl topY topX)

  VU Set -> case (topX, topY) of

    (VU Set,  VU Set)  -> VTop
    (VU Prop, VU Prop) -> VTop

    (VPi x i a au b, VPi x' i' a' au' b') | i == i' ->
      case univConv au au' of
        Nothing    -> VEq topA topX topY
        Just False -> VBot
        Just True  ->
          vEx "p" (vEq l (VU au) a a') \p →
          vAll (pick x x') a \x → vEq l (VU Set) (b x) (b' (vCoe l au a a' p x))

    (VSg x a au b bu, VSg x' a' au' b' bu') ->
      case (univConv au au', univConv bu bu') of
        (Just b1, Just b2)
          | b1 && b2  ->
            vEx "p" (vEq l (VU au) a a') \p →
            vAll (pick x x') a \x → vEq l (VU Set) (b x) (b' (vCoe l au a a' p x))
          | otherwise -> VBot
        _ -> VEq topA topX topY

    (VNe{}, _) -> VEq topA topX topY
    (_, VNe{}) -> VEq topA topX topY
    _          -> VBot

  VU _ -> VEq topA topX topY

  VPi x i a au b ->
    vAll x a \x -> vEq l (b x) (vApp topX x au i) (vApp topY x au i)

  VSg x a au b bu ->
    let sgu = au <> bu
        p1x = vProj1 topX sgu
        p1y = vProj1 topY sgu
        p2x = vProj2 topX sgu
        p2y = vProj2 topY sgu
    in vEx "p" (vEq l a p1x p1y) \p -> vEq l (b p1y) (vCoe l bu (b p1x) (b p1y) p p2x) p2y

  VNe{} -> VEq topA topX topY
  _     -> error "impossible"

tryRegularity :: Lvl -> U -> Val -> Val -> Val -> Val -> Val
tryRegularity l ~u a b ~p ~t =
  case runIO (conversion l Set a b) of
    No    -> VNe (HCoe u a b p t) SNil
    Dunno -> VNe (HCoe u a b p t) SNil
    Yes   -> t

-- | Note: coe composition and canonical coe rules are *not* confluent!
--   We can only use composition if the inner coe is rigidly *not* canonical.
--   Coe refl on the other hand is confluent with everything.
--   Right now we ignore the rigidity check.
vCoe :: Lvl -> U -> Val -> Val -> Val -> Val -> Val
vCoe l topU topA topB topP t = case topU of
  Prop -> vProj1 topP Prop □ t
  Set -> case (topA, topB) of

    -- canonical coercions
    (VPi x i a au b, VPi x' i' a' au' b')
      | i /= i'   -> vExfalso topU topB topP
      | otherwise -> case univConv au au' of
          Nothing    -> VNe (HCoe topU topA topB topP t) SNil
          Just False -> vExfalso topU topB topP
          Just True  ->
            VLam (pick x x') i a' au \ ~a1 ->
            let ~p1 = vProj1 topP Prop
                ~p2 = vProj2 topP Prop
                ~a0 = vCoe l au a' a (vSym (VU au) a a' p1) a1
            in vCoe l Set (b a0) (b' a1) (vApp p2 a0 au Expl) (vApp t a0 au i)

    (VSg x a au b bu, VSg x' a' au' b' bu') ->
      case (univConv au au', univConv bu bu') of
        (Just b1, Just b2)
          | b1 && b2 ->
             let p1  = vProj1 t Set
                 p2  = vProj2 t Set
                 p1' = vCoe l au a a' (vProj1 topP Prop) p1
                 p2' = vCoe l bu (b p1) (b' p1') (vProj2 topP Prop) p2
             in VPair p1' au p2' bu
          | otherwise -> vExfalso topU topB topP
        _ -> VNe (HCoe topU topA topB topP t) SNil

    -- coe lifting rules
    (topA, topB) -> case t of
      VNe (HCoe _ a' _ q t) SNil ->
        let newp = vTrans VSet a' topA topB q topP
        in tryRegularity l Set a' topB newp t
      _ -> tryRegularity l Set topA topB topP t

  _ -> VNe (HCoe topU topA topB topP t) SNil


eval :: Vals -> Lvl -> Tm -> Val
eval vs l = go where
  go = \case
    Var x          -> vVar x vs
    Let x a au t u -> goBind u (go t)
    Meta m         -> vMeta m
    Pi x i a au b  -> VPi x i (go a) au (goBind b)
    Lam x i a au t -> VLam x i (go a) au (goBind t)
    App t u uu i   -> vApp (go t) (go u) uu i
    Skip t         -> eval (VSkip vs) (l + 1) t
    U u            -> VU u
    Top            -> VTop
    Tt             -> VTt
    Bot            -> VBot
    Eq             -> VLamIS "A" VSet \ ~a -> VLamES "x" a \ ~x -> VLamES "y" a \ ~y ->
                      vEq l a x y
    Coe u          -> VLamIS "A" (VU u) \ ~a -> VLamIS "B" (VU u) \ ~b ->
                      VLamEP "p" (VEq (VU u) a b) \ ~p -> VLam "t" Expl a u \ ~t ->
                      vCoe l u a b p t
    Exfalso u      -> VLamIS "A" (VU u) \ ~a -> VLamEP "p" VBot \ ~t ->
                      vExfalso u a t
    Refl           -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x -> vRfl a x
    Sym            -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamEP "p" (VEq a x y) \ ~p ->
                      vSym a x y p
    Trans          -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamIS "z" a \ ~z ->
                      VLamEP "p" (VEq a x y) \ ~p -> VLamEP "q" (VEq a y z) \ ~q ->
                      vTrans a x y z p q
    Ap             -> VLamIS "A" VSet \ ~a -> VLamIS "B" VSet \ ~b ->
                      VLamES "f" (VPiES "_" a (const b)) \ ~f -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamEP "p" (VEq a x y) \ ~p ->
                      vAp a b f x y p
    Sg x a au b bu -> VSg x (go a) au (goBind b) bu
    Pair t tu u uu -> VPair (go t) tu (go u) uu
    Proj1 t tu     -> vProj1 (go t) tu
    Proj2 t tu     -> vProj2 (go t) tu

  goBind t v = eval (VDef vs v) (l + 1) t

quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case force d v of
    VNe h sp ->
      let goSp SNil = case h of
            HMeta m        -> Meta m
            HVar x         -> Var (d - x - 1)
            HCoe u a b p t -> tCoe u (go a) (go b) (go p) (go t)
            HAxiom ax      -> axiomToTm ax

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


-- Conversion
--------------------------------------------------------------------------------

univConv :: U -> U -> Maybe Bool
univConv Set       Set        = Just True
univConv Set       Prop       = Just False
univConv Prop      Set        = Just False
univConv (UMax xs) (UMax xs') = True <$ guard (xs == xs')
univConv _         _          = Nothing

conversion :: Lvl -> U -> Val -> Val -> IO Perhaps
conversion lvl un l r = (Yes <$ goTop lvl un l r) `catch` pure where

  goTop :: Lvl -> U -> Val -> Val -> IO ()
  goTop lvl un l r = go un l r where

    goU :: U -> U -> IO ()
    goU u u' = case univConv (forceU u) (forceU u') of
      Nothing    -> throw Dunno
      Just False -> throw No
      _          -> pure ()

    go :: U -> Val -> Val -> IO ()
    go un t t' = case forceU un of
      Prop -> pure ()
      _    -> case (force lvl t, force lvl t') of
        (VLam x _ a au t, VLam x' _ _ _ t') -> goBind (pick x x') a au un t t'
        (VLam x i a au t, t')               -> goBind x a au un t (\ ~v -> vApp t' v au i)
        (t, VLam x' i' a' au' t')           -> goBind x' a' au' un (\ ~v -> vApp t v au' i') t'

        (VPi x i a au b, VPi x' i' a' au' b') | i == i' -> do
          goU au au'
          go Set a a'
          goBind (pick x x') a au Set b b'

        (VSg x a au b bu, VSg x' a' au' b' bu') -> do
          goU au au'  >> goU bu bu'
          go Set a a' >> goBind (pick x x') a au Set b b'

        (VPair t tu u uu, VPair t' tu' u' uu') -> do
          goU tu tu' >> goU uu uu'
          go tu t t' >> go uu u u'

        (VPair t tu u uu, t') -> do
          let sgu = tu <> uu
          go tu t (vProj1 t' sgu) >> go uu u (vProj2 t' sgu)

        (t', VPair t tu u uu) -> do
          let sgu = tu <> uu
          go tu (vProj1 t' sgu) t >> go uu (vProj2 t' sgu) u

        (VU u, VU u') -> goU u u'
        (VTop, VTop)  -> pure ()
        (VTt, VTt)    -> pure ()
        (VBot, VBot)  -> pure ()

        (VEq a x y, VEq a' x' y') -> go Set a a' >> go Set x x' >> go Set y y'
        (VNe h sp, VNe h' sp') -> case (h, h') of

          (HVar x, HVar x') | x == x' -> goSp  sp sp'
          (HAxiom ax, HAxiom ax') -> case (ax, ax') of

            (ARfl, ARfl)              -> goSp sp sp'
            (ASym, ASym)              -> goSp sp sp'
            (AAp , AAp )              -> goSp sp sp'
            (AExfalso u, AExfalso u') -> goU u u' >> goSp sp sp'
            _                         -> throw No

          (HCoe u a b p t, HCoe u' a' b' p' t') -> do
            goU u u' >> go Set a a' >> go Set b b' >> go Prop p p' >> go u t t'

          (HMeta m, HMeta m') | m == m'   -> goSp sp sp'
                              | otherwise -> throw Dunno

          (HMeta m, h') -> throw Dunno
          (h, HMeta m') -> throw Dunno
          _             -> throw No

        (VNe (HMeta m) sp, t')  -> throw Dunno
        (t, VNe (HMeta m') sp') -> throw Dunno
        (t, t')                 -> throw No

    goBind :: Name -> VTy -> U -> U -> (Val -> Val) -> (Val -> Val) -> IO ()
    goBind x a au un t t' =
      let v = VVar lvl in goTop (lvl + 1) un (t v) (t' v)

    goSp :: Spine -> Spine -> IO ()
    goSp sp sp' = case (sp, sp') of
      (SNil, SNil)                                   -> pure ()
      (SApp sp u uu i, SApp sp' u' uu' i') | i == i' -> goSp sp sp' >>
                                                        goU uu uu' >> go uu u u'
      _                                              -> error "impossible"
