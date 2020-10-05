
module Evaluation where

import Control.Exception
import Control.Monad
import qualified Data.IntSet as IS

import Types
import ElabState

-- import Debug.Trace

valDbg :: Val -> String
valDbg = \case
  VNe h _   -> case h of
    HVar x    -> "VNe HVar " ++ show x
    HMeta _   -> "VNe HMeta"
    HAxiom ax -> "VNe " ++ show ax
    HCoe{}    -> "VNe HCoe"
  VPi{}     -> "VPi"
  VLam{}    -> "VLam"
  VU{}      -> "VU"
  VTop      -> "VTop"
  VTt       -> "VTt"
  VBot      -> "VBot"
  VEqGlue{} -> "VEqGlue"
  VEq{}     -> "VEq"
  VSg{}     -> "VSg"
  VPair{}   -> "VPair"
  VNat{}    -> "VNat"
  VZero{}   -> "VZero"
  VSuc{}    -> "VSuc"


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

{-
Choices about forcing.

Approach 1: in evaluation, everything which is matched on is assumed
to be forced. Pro: neat. Con: requires forcing universes in Sg, Pi, which
is a bit too deep.

Approach 2: in evaluation, every Val is assumed to be forced, but universes
are *not*. Hence, even in eval every U match must force. Pro: perhaps more efficient?
Con: less elegant.

I like 1 because evaluation incurs zero overhead when we evaluate meta-free core syntax.
Perhaps it would be the most efficient to summarize every stuck term in a VStuck,
which would make forcing more efficient.


-}


-- | Force the outermost constructor. Does *not* force universes! Whenever
--   we match on U, even in evaluation, we must force it!
force :: Lvl -> Val -> Val
force l = \case
  VNe h sp -> case h of
    HMeta m -> case runLookupMeta m of
      Unsolved{} -> VNe h sp
      Solved v   -> force l (vAppSp v sp)
    HCoe u a b p t ->
      vAppSp (vCoe l u (force l a) (force l b) (force l p) (force l t)) sp
    _ -> VNe h sp
  VEq a t u -> vEq l (force l a) (force l t) (force l u)
  v         -> v

-- | Note: we *always* have to forceU on match site! Force does not touch universes.
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
  v             -> error "impossible"

vProj2 :: Val -> U -> Val
vProj2 v vu = case v of
  VPair t _ u _ -> u
  VNe h sp      -> VNe h (SProj2 sp vu)
  _             -> error "impossible"

vProjField :: Val -> Name -> Int -> U -> Val
vProjField v x i vu = case v of
  VNe h sp        -> VNe h (SProjField sp x i vu)
  VPair t tu u uu -> case i of
    0 -> t
    i -> vProjField u x (i - 1) uu
  _ -> error "impossible"

vInd :: U -> Val -> Val -> Val -> Val -> Val
vInd u p z s n = case n of
  VZero    -> z
  VSuc n   -> vApp (s `vAppSI` n) (vInd u p z s n) u Expl
  VNe h sp -> VNe h (SInd sp u p z s)
  v        -> error (valDbg v)

vAppSp :: Val -> Spine -> Val
vAppSp h = go where
  go SNil                    = h
  go (SApp sp u uu i)        = vApp (go sp) u uu i
  go (SProj1 sp spu)         = vProj1 (go sp) spu
  go (SProj2 sp spu)         = vProj2 (go sp) spu
  go (SProjField sp x i spu) = vProjField (go sp) x i spu
  go (SInd sp u p z s)       = vInd u p z s (go sp)

vAppSI ~t ~u = vApp t u Set  Impl
vAppSE ~t ~u = vApp t u Set  Expl
vAppPI ~t ~u = vApp t u Prop Impl
vAppPE ~t ~u = vApp t u Prop Expl

vExfalso u a t     = vApp (VAxiom (AExfalso u) `vAppSI` a) t u Expl
vRefl    a t       = VAxiom ARefl `vAppSI`  a `vAppSI`  t
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

vEq :: Lvl -> Val -> Val -> Val -> Val
vEq l topA ~topX ~topY =
  let stuck = VEq topA topX topY
      glue  = VEqGlue topA topX topY in
  case topA of
    VU topU -> case forceU topU of
      Prop ->
        glue (vAnd (vImpl topX topY) (vImpl topY topX))

      Set -> case (topX, topY) of
        (VU Set,  VU Set)  -> glue VTop
        (VU Prop, VU Prop) -> glue VTop
        (VNat   , VNat   ) -> glue VTop

        (VPi x i a (forceU -> au) b, VPi x' i' a' (forceU -> au') b') | i == i' ->
          case univConv au au' of
            Nothing    -> stuck
            Just False -> glue VBot
            Just True  -> glue (
              vEx "p" (vEq l (VU au) a a') \p →
              vAll (pick x x') a \x → vEq l (VU Set) (b x) (b' (vCoe l au a a' p x)))

        (VSg x a (forceU -> au) b (forceU -> bu),
         VSg x' a' (forceU -> au') b' (forceU -> bu')) ->
          case (univConv au au', univConv bu bu') of
            (Just b1, Just b2)
              | b1 && b2  ->
                glue (
                  vEx "p" (vEq l (VU au) a a') \p →
                  vAll (pick x x') a \x → vEq l (VU bu) (b x) (b' (vCoe l au a a' p x)))
              | otherwise -> glue  VBot
            _ -> stuck

        (VNe{}, _) -> stuck
        (_, VNe{}) -> stuck
        _          -> glue VBot

      _ -> stuck

    VNat -> case (topX, topY) of
      (VZero , VZero  ) -> glue VTop
      (VSuc n, VSuc n') -> vEq l VNat n n'
         -- error (valDbg n ++ " " ++ valDbg n')
      (VSuc _, VZero  ) -> glue VBot
      (VZero , VSuc _ ) -> glue VBot
      _                 -> stuck

    -- note that funext is always by explicit function!
    VPi x i a au b -> glue (
      VPi x Expl a au \ ~x -> vEq l (b x) (vApp topX x au i) (vApp topY x au i))

    VSg x a (forceU -> au) b (forceU -> bu) ->
      let ~p1x = vProj1 topX Set
          ~p1y = vProj1 topY Set
          ~p2x = vProj2 topX Set
          ~p2y = vProj2 topY Set in
      case (au, bu) of
        (Set,  Prop) -> vEq l a p1x p1y
        (Set,  Set ) -> glue (
                         vEx "p" (vEq l a p1x p1y) \p ->
                         vEq l (b p1y)
                               (vCoe l bu (b p1x) (b p1y)
                                  (vAp a (VU bu) (VLam x Expl a au b) p1x p1y p) p2x)
                               p2y)
        (Prop, Prop) -> error "impossible"
        (Prop, Set ) -> vEq l (b p1x) p2x p2y
        _            -> stuck

    VNe{} -> stuck
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
vCoe :: Dbg => Lvl -> U -> Val -> Val -> Val -> Val -> Val
vCoe l topU topA topB topP t = case forceU topU of
  Prop -> vProj1 topP Prop `vAppPI` t
  Set -> case (topA, topB) of

    -- canonical coercions
    (VPi x i a (forceU -> au) b, VPi x' i' a' (forceU -> au') b')
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

    (VSg x a (forceU -> au) b (forceU -> bu),
     VSg x' a' (forceU -> au') b' (forceU -> bu')) ->
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


eval :: Dbg => Vals -> Lvl -> Tm -> Val
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
                      VLamEP "p" (vEq l (VU u) a b) \ ~p -> VLam "t" Expl a u \ ~t ->
                      vCoe l u a b p t
    Exfalso u      -> VLamIS "A" (VU u) \ ~a -> VLamEP "p" VBot \ ~t ->
                      vExfalso u a t
    Refl           -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x -> vRefl a x
    Sym            -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamEP "p" (vEq l a x y) \ ~p ->
                      vSym a x y p
    Trans          -> VLamIS "A" VSet \ ~a -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamIS "z" a \ ~z ->
                      VLamEP "p" (vEq l a x y) \ ~p -> VLamEP "q" (vEq l a y z) \ ~q ->
                      vTrans a x y z p q
    Ap             -> VLamIS "A" VSet \ ~a -> VLamIS "B" VSet \ ~b ->
                      VLamES "f" (VPiES "_" a (const b)) \ ~f -> VLamIS "x" a \ ~x ->
                      VLamIS "y" a \ ~y -> VLamEP "p" (vEq l a x y) \ ~p ->
                      vAp a b f x y p
    Sg x a au b bu     -> VSg x (go a) au (goBind b) bu
    Pair t tu u uu     -> VPair (go t) tu (go u) uu
    Proj1 t tu         -> vProj1 (go t) tu
    Proj2 t tu         -> vProj2 (go t) tu
    ProjField t x i tu -> vProjField (go t) x i tu

    Nat           -> VNat
    Zero          -> VZero
    Suc           -> VLamES "n" VNat VSuc

    Ind u ->
        let pty   = VPiES "_" VNat (const (VU u))
            zty p = vAppSE p VZero
            sty p = VPiIS "n" VNat \ ~n -> VPi "_" Expl (vAppSE p n) u \_ ->
                    vAppSE p (VSuc n)

            in VLam "P" Expl pty Set   \ ~p ->
               VLam "z" Expl (zty p) u \ ~z ->
               VLam "s" Expl (sty p) u \ ~s ->
               VLam "n" Expl VNat Set  \ ~n ->
               vInd u p z s n

  goBind t v = eval (VDef vs v) (l + 1) t

quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case force d v of
    VNe h sp ->
      let goSp SNil = case h of
            HMeta m        -> Meta m
            HVar x         -> Var (d - x - 1)
            HCoe u a b p t -> tCoe (forceU u) (go a) (go b) (go p) (go t)
            HAxiom ax      -> case ax of
              ARefl      -> Refl
              ASym       -> Sym
              ATrans     -> Trans
              AAp        -> Ap
              AExfalso u -> Exfalso (forceU u)

          goSp (SApp sp u uu i)        = App (goSp sp) (go u) (forceU uu) i
          goSp (SProj1 sp spu)         = Proj1 (goSp sp) (forceU spu)
          goSp (SProj2 sp spu)         = Proj2 (goSp sp) (forceU spu)
          goSp (SProjField sp x i spu) = ProjField (goSp sp) x i (forceU spu)
          goSp (SInd sp u p z s)       = tInd (forceU u) (go p) (go z) (go s) (goSp sp)

      in goSp sp

    VLam x i a au t -> Lam x i (go a) (forceU au) (goBind t)
    VPi x i a au b  -> Pi x i (go a) (forceU au) (goBind b)
    VU u            -> U (forceU u)
    VTop            -> Top
    VTt             -> Tt
    VBot            -> Bot
    VEqGlue a t u b -> go b
    VEq a t u       -> tEq (go a) (go t) (go u)

    VSg x a au b bu -> Sg x (go a) (forceU au) (goBind b) (forceU bu)
    VPair t tu u uu -> Pair (go t) (forceU tu) (go u) (forceU uu)

    VNat            -> Nat
    VZero           -> Zero
    VSuc n          -> tSuc (go n)

  goBind t = quote (d + 1) (t (VVar d))


-- Conversion
--------------------------------------------------------------------------------

univConv :: U -> U -> Maybe Bool
univConv u u' = case (u, u') of
  (Set      , Set     ) -> Just True
  (Set      , Prop    ) -> Just False
  (Prop     , Set     ) -> Just False
  (UMax xs  , UMax xs') -> True <$ guard (xs == xs')
  (_        , _       ) -> Nothing

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
      un   -> case (force lvl t, force lvl t') of
        (VEqGlue _ _ _ b, t') -> go Set b t'
        (t, VEqGlue _ _ _ b') -> go Set t b'

        (VEq a x y, VEq a' x' y') -> go Set a a' >> go Set x x' >> go Set y y'

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

        (VNe h sp, VNe h' sp') -> case (h, h') of

          (HVar x, HVar x') | x == x' -> goSp un sp sp'
          (HAxiom ax, HAxiom ax') -> case (ax, ax') of

            (ARefl, ARefl)            -> goSp un sp sp'
            (ASym, ASym)              -> goSp un sp sp'
            (AAp , AAp )              -> goSp un sp sp'
            (AExfalso u, AExfalso u') -> goU u u' >> goSp un sp sp'
            _                         -> throw No

          (HCoe u a b p t, HCoe u' a' b' p' t') -> do
            goU u u' >> go Set a a' >> go Set b b' >> go Prop p p' >> go u t t'

          (HMeta m, HMeta m') | m == m'   -> goSp un sp sp'
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

    -- TODO BUG: add other Spine arg!!
    goProjField :: Spine -> U -> U -> Int -> IO ()
    goProjField _               spu spu' 0 = goU spu spu'
    goProjField (SProj2 sp spu) _   spu' i = goProjField sp spu spu' (i - 1)
    goProjField _               _   _    _ = throw No

    -- MISSING: relevance check!
    goSp :: U -> Spine -> Spine -> IO ()
    goSp (forceU -> Prop) _ _    = pure ()
    goSp (forceU -> un  ) sp sp' = case (sp, sp') of
      (SNil, SNil)                                   -> pure ()
      (SApp sp u uu i, SApp sp' u' uu' i') | i == i' -> goU uu uu' >> go uu u u'
                                                        >> goSp un sp sp'
      (SInd sp u p z s, SInd sp' u' p' z' s') ->
        goSp Set sp sp' >> goU u u' >> go Set p p' >> go u z z' >> go u s s'

      (SProj1 sp spu, SProj1 sp' spu')               -> goU spu spu' >> goSp spu sp sp'
      (SProj2 sp spu, SProj2 sp' spu')               -> goU spu spu' >> goSp spu sp sp'
      (SProjField sp _ i spu,
       SProjField sp' _ i' spu') | i == i'           -> goU spu spu' >> goSp spu sp sp'
      (SProj1 sp spu, SProjField sp' x i spu')       -> goProjField sp spu spu' i
      (SProjField sp x i spu, SProj1 sp' spu')       -> goProjField sp' spu' spu i
      _                                              -> throw No
