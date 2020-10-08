
module Eval (
    ($$), vApp, vProj1, vProj2, vProjField
  , vCoe, vEq, forceU, conv, force, fforce, vSp, vCoeP, eval, quote
  ) where

import Control.Monad
import IO
import qualified Data.IntSet as IS

import qualified Syntax as S
import Common
import ElabState
import Value
import Exceptions

-- Core inspection:
--   - inlined forceU is large code bloat
--     IDEA: manually fuse forceU and matchU, try to make it small
--   - IS.foldl' is big but not too bad
--   - ByteString is pain in the ass, "pick" and literals suck; use custom inductive Name type instead
--     (right now the ByteString fields are made lazy to stop the inlined literal madness!)
--   - pattern synonyms are completely strict constructors with Strict unless we write out the constructing direction manually
--   - eval floats out all closures before the case split! It's shitty as hell. GHC.Magic does not prevent this.
--   - fno-full-laziness is a shitshow
--   - Unboxed sums have mandatory lazy lifted fields! We also can't unpack into unboxed sum. Solution: get rid
--     Unboxed tuples are also lazy in lifted fields.
--     of unboxed sums for closures. Use instead manually unsafeCoerced and unpacked data type.

-- IDEA: make evaluation utterly and totally strict and CBV, with the exception of let bindings.
--       instead, rely on Unfold to limit computation; Unfold behaves like an explicit thunk!
--       Also, we create thunks in elaboration, when we do "substitution", e.g. when checking Pi.
--       However, eval only creates thunks in a) let b) Unfold, nowhere else.


-- TODO: benchmark to see if S usage helps! It definitely improves Core, but there could be some STG/cmm
--    pass which makes this unnecessary.

-- RULES of the game:
--    - language Strict
--    - No recursive local functions with capture. GHC is prone to leaving closures around even in STG output
--    - User-defined sum types wrapped with S everywhere. TODO: write Template Haskell for S-wrapping! This
--      should also make it easier to benchmarked S-wrapping versus no wrapping. By inspecting STG, it seems
--      that S-wrapping completely eliminates laziness overhead in all known calls. Only unknown calls retain
--      thunk checks.
--    - NEVER RETURN S FROM RUNIO
--    - TODO: USE INSPECTION TESTING
--    - Use S-wrapping on things which are often not known to be forced, because they come from function args, not from
--      strict data fields. E.g. FlexHead always comes from a Val and is thus known to be strict, in contrast
--      vApp gets an U and an Icit from anywhere.


-- Variables
--------------------------------------------------------------------------------

vLocalVar :: Env -> Ix -> Val
vLocalVar (Snoc _ v)   0 = S v
vLocalVar (Snoc env _) x = vLocalVar env (x - 1)
vLocalVar _ _            = impossible

vMeta :: Meta -> Val
vMeta x = S $ runIO $ readMeta x >>= \case
  MEUnsolved{} -> pure $ WFlex (FHMeta x) SNil
  MESolved v   -> pure $ WUnfold (UHMeta x) SNil (unS v)
{-# inline vMeta #-}

vTopDef :: Lvl -> Val
vTopDef x = S $ runIO $ readTop x >>= \case
  TEDef v _ _ _ _ -> pure $ WUnfold (UHTopDef x) SNil v
  _               -> impossible
{-# inline vTopDef #-}


-- Functions
--------------------------------------------------------------------------------

infixl 2 $$
($$) :: Closure -> Val -> Val
($$) cl u = case cl of
  Fun t         -> t u
  Close env l t -> eval (Snoc env (unS u)) l t
{-# inline ($$) #-}

vApp :: Val -> Val -> S.U -> Icit -> Val
vApp t u un i = case t of
  Lam _ _ _ _ t -> t $$ u
  Rigid h sp    -> Rigid  h (SApp sp u un i)
  Flex h sp     -> Flex   h (SApp sp u un i)
  Unfold h sp t -> Unfold h (SApp sp u un i) (unS (vApp (S t) u un i))
  _             -> impossible

-- Projections
--------------------------------------------------------------------------------

vProj1 :: Val -> Val
vProj1 t = case t of
  Pair t _ u _  -> t
  Rigid h sp    -> Rigid  h (SProj1 sp)
  Flex h sp     -> Flex   h (SProj1 sp)
  Unfold h sp t -> Unfold h (SProj1 sp) (unS (vProj1 (S t)))
  _             -> impossible

vProj2 :: Val -> Val
vProj2 t = case t of
  Pair t _ u _  -> u
  Rigid h sp    -> Rigid  h (SProj2 sp)
  Flex h sp     -> Flex   h (SProj2 sp)
  Unfold h sp t -> Unfold h (SProj2 sp) (unS (vProj2 (S t)))
  _             -> impossible

vProjField :: Val -> Name -> Int -> Val
vProjField t x n = case t of
  Pair t tu u uu -> case n of 0 -> t
                              n -> vProjField u x (n - 1)
  Rigid h sp     -> Rigid  h (SProjField sp x n)
  Flex h sp      -> Flex   h (SProjField sp x n)
  Unfold h sp t  -> Unfold h (SProjField sp x n) (unS (vProjField (S t) x n))
  _              -> impossible

-- Universe matching
--------------------------------------------------------------------------------

data MatchU = MUProp | MUSet | MUDiff | MUUMax IS.IntSet

matchUMaxSet :: S.UMax -> MatchU
matchUMaxSet xs = case forceUMax xs of
  S.Set     -> MUSet
  S.Prop    -> MUDiff
  S.UMax xs -> MUUMax xs
{-# noinline matchUMaxSet #-}

matchUMaxProp :: S.UMax -> MatchU
matchUMaxProp xs = case forceUMax xs of
  S.Set     -> MUDiff
  S.Prop    -> MUProp
  S.UMax xs -> MUUMax xs
{-# noinline matchUMaxProp #-}

matchUMax :: S.UMax -> S.U -> MatchU
matchUMax xs u = case forceUMax xs of
  S.Set -> case u of
    S.Set      -> MUSet
    S.Prop     -> MUDiff
    S.UMax xs' -> matchUMaxSet xs'
  S.Prop -> case u of
    S.Set      -> MUDiff
    S.Prop     -> MUProp
    S.UMax xs' -> matchUMaxProp xs'
  S.UMax xs -> MUUMax xs
{-# noinline matchUMax #-}

-- | Match universes, but don't check equality of neutrals, instead immediately
--  flexibly fail on any UMax. We need this kind of comparison in evaluation,
--  because computation cannot progress in the presence of UMax. The elaborate
--  implementation serves to reduce code bloat in vEq and vCoe (halves code size!)
matchU :: S.U -> S.U -> MatchU
matchU u u' = case u of
  S.Set -> case u' of
    S.Set      -> MUSet
    S.Prop     -> MUDiff
    S.UMax xs' -> matchUMaxSet xs'
  S.Prop -> case u' of
    S.Set      -> MUDiff
    S.Prop     -> MUProp
    S.UMax xs' -> matchUMaxProp xs'
  S.UMax xs -> matchUMax xs u'


-- Coercion
--------------------------------------------------------------------------------

vCoe :: Lvl -> Val -> Val -> Val -> Val -> Val
vCoe l a b p t = case (a, b) of
  (topA@(Pi x i a au b), topB@(Pi x' i' a' au' b'))
    | i /= i'   -> Exfalso S.Set (Pi x' i' a' au' b') p
    | otherwise -> case matchU au au' of
        MUSet     -> Lam (pick x x') i a' S.Set $ Fun \a1 ->
                     let p1 = vProj1 p
                         p2 = vProj2 p
                         a0 = vCoe l a' a (Sym Set a a' p1) a1
                     in vCoe l (b $$ a0) (b' $$ a1) (vApp p2 a0 S.Set Expl) (vApp t a0 S.Set i)
        MUProp    -> Lam (pick x x') i a' S.Prop $ Fun \a1 ->
                     let p1 = vProj1 p
                         p2 = vProj2 p
                         a0 = vCoeP (Sym Prop a a' p1) a1
                     in vCoe l (b $$ a0) (b' $$ a1) (vApp p2 a0 S.Prop Expl) (vApp t a0 S.Prop i)
        MUDiff    -> Exfalso S.Set topB p
        MUUMax au -> Flex (FHCoeUMax au topA topB p t) SNil

  (topA@(Sg x a au b bu), topB@(Sg x' a' au' b' bu')) ->
    case (matchU au au', matchU bu bu') of
      (MUSet, MUSet)   -> let p1  = vProj1 t
                              p2  = vProj2 t
                              p1' = vCoe l a a' (vProj1 p) p1
                              p2' = vCoe l (b $$ p1) (b' $$ p1') (vProj2 p) p2
                          in Pair p1' S.Set p2' S.Set
      (MUSet, MUProp)  -> let p1  = vProj1 t
                              p2  = vProj2 t
                              p1' = vCoe l a a' (vProj1 p) p1
                              p2' = vCoeP (vProj2 p) p2
                          in Pair p1' S.Set p2' S.Prop
      (MUProp, MUSet)  -> let p1  = vProj1 t
                              p2  = vProj2 t
                              p1' = vCoeP (vProj1 p) p1
                              p2' = vCoe l (b $$ p1) (b' $$ p1') (vProj2 p) p2
                          in Pair p1' S.Prop p2' S.Set
      (MUProp, MUProp) -> impossible
      (MUDiff, _)      -> Exfalso S.Set topB p
      (_ , MUDiff)     -> Exfalso S.Set topB p
      (MUUMax au, _)   -> Flex (FHCoeUMax au topA topB p t) SNil
      (_, MUUMax bu)   -> Flex (FHCoeUMax bu topA topB p t) SNil

  (Flex h sp    , b            ) -> Flex h (SCoeSrc sp b p t)
  (Unfold h sp a, b            ) -> Unfold h (SCoeSrc sp b p t) (unS (vCoe l (S a) b p t))
  (a            , Flex h sp    ) -> Flex h (SCoeTgt a sp p t)
  (a            , Unfold h sp b) -> Unfold h (SCoeTgt a sp p t) (unS (vCoe l a (S b) p t))
  (a            , b            ) -> vCoeComp l a b p t

-- | Try to compute coercion composition.
vCoeComp :: Lvl -> Val -> Val -> Val -> Val -> Val
vCoeComp l a b p t = case t of
  Flex h sp                     -> Flex h (SCoeComp a b p sp)
  Unfold h sp t                 -> Unfold h (SCoeComp a b p sp) (unS (vCoeComp l a b p (S t)))
  Rigid (RHCoe a' _ p' t') SNil -> vCoeRefl l a' b (Trans Set a' a b p' p) t'
  t                             -> vCoeRefl l a b p t

-- | Try to compute reflexive coercion.
vCoeRefl :: Lvl -> Val -> Val -> Val -> Val -> Val
vCoeRefl l a b p t = S $ runIO do
  (unS t <$ convIO l DontUnfold a b) `catch` \case
    ConvDiff    -> pure $ WRigid (RHCoe a b p t) SNil
    ConvMeta x  -> pure $ WFlex (FHCoeRefl x a b p t) SNil
    ConvUMax xs -> pure $ WFlex (FHCoeUMax xs a b p t) SNil
    ConvSame    -> impossible

-- | coeP : {A B : Prop} -> A = B -> A -> B
vCoeP :: Val -> Val -> Val
vCoeP p t = vApp (vProj1 p) t S.Prop Expl
{-# inline vCoeP #-}


-- Equality type
--------------------------------------------------------------------------------

vEq :: Lvl -> Val -> Val -> Val -> Val
vEq l a t u = case a of
  U un -> case forceU un of
    S.Set     -> vEqSet l t u
    S.Prop    -> vEqProp t u
    S.UMax xs -> Flex (FHEqUMax xs a t u) SNil

  -- funext always computes to Expl function
  topA@(Pi x i a au b) -> Eq topA t u $
    unS (Pi x Expl a au $ Fun \x -> vEq l (b $$ x) (vApp t x au i) (vApp u x au i))

  -- equality of Prop fields is automatically skipped
  topA@(Sg x a (forceU -> !au) b (forceU -> !bu)) ->
    let p1t = vProj1 t
        p1u = vProj1 u
        p2t = vProj2 t
        p2u = vProj2 u in
    case (au, bu) of
      (S.Set, S.Prop)  -> vEq l a p1t p1u
      (S.Set, S.Set )  -> Eq topA t u $
                          unS (PiEP NP (vEq l a p1t p1u) \p ->
                               vEq l (b $$ p1u)
                                     (vCoe l (b $$ p1t) (b $$ p1u)
                                             (Ap a Set (Lam x Expl a S.Set b) p1t p1u p) p2t)
                                     p2u)
      (S.Prop, S.Set)  -> vEq l (b $$ p1t) p2t p2u
      (S.Prop, S.Prop) -> impossible
      (S.UMax xs, _)   -> Flex (FHEqUMax xs topA t u) SNil
      (_, S.UMax xs)   -> Flex (FHEqUMax xs topA t u) SNil

  Rigid  h sp   -> Rigid  h (SEqType sp t u)
  Flex   h sp   -> Flex   h (SEqType sp t u)
  Unfold h sp a -> Unfold h (SEqType sp t u) (unS (vEq l (S a) t u))
  _             -> impossible

vEqProp :: Val -> Val -> Val
vEqProp a b = Eq Prop a b (unS (andP (implies a b) (implies b a)))
{-# inline vEqProp #-}

-- | Equality of sets.
vEqSet :: Lvl -> Val -> Val -> Val
vEqSet l a b = case (a, b) of
  (U u, U u') -> case matchU u u' of
    MUProp     -> Eq Set Prop Prop WTop
    MUSet      -> Eq Set Set Set WTop
    MUDiff     -> Eq Set (U u) (U u') WBot
    MUUMax xs  -> Flex (FHEqUMax xs Set (U u) (U u')) SNil

  (topA@(Pi x i a au b), topB@(Pi x' i' a' au' b')) ->
    let eq = Eq Set topA topB in
    case matchU au au' of
      MUProp      -> eq $ unS (SgPP NP (vEqProp a a') \p ->
                     PiEP (pick x x') a \x -> vEqSet l (b $$ x) (b' $$ vCoeP p x))
      MUSet       -> eq $ unS (SgPP NP (vEqSet l a a') \p ->
                     PiEP (pick x x') a \x -> vEqSet l (b $$ x) (b' $$ vCoe l a a' p x))
      MUDiff      -> eq WBot
      MUUMax au   -> Flex (FHEqUMax au Set topA topB) SNil

  (topA@(Sg x a au b bu), topB@(Sg x' a' au' b' bu')) ->
    let eq = Eq Set topA topB in
    case (matchU au au', matchU bu bu') of
      (MUSet,  MUSet )  -> eq $ unS (SgPP NP (vEqSet l a a') \p ->
                           PiEP (pick x x') a \x -> vEqSet l (b $$ x) (b' $$ vCoe l a a' p x))
      (MUSet,  MUProp)  -> eq $ unS (SgPP NP (vEqSet l a a') \p ->
                           PiEP (pick x x') a \x -> vEqProp (b $$ x) (b' $$ vCoeP p x))
      (MUProp, MUSet )  -> eq $ unS (SgPP NP (vEqProp a a') \p ->
                           PiEP (pick x x') a \x -> vEqSet l (b $$ x) (b' $$ vCoe l a a' p x))
      (MUProp, MUProp)  -> impossible
      (MUDiff, _    )   -> eq WBot
      (_    , MUDiff)   -> eq WBot
      (MUUMax au, _)    -> Flex (FHEqUMax au Set topA topB) SNil
      (_, MUUMax bu)    -> Flex (FHEqUMax bu Set topA topB) SNil

  (Flex h sp    , b            ) -> Flex   h (SEqSetLhs sp b)
  (Unfold h sp a, b            ) -> Unfold h (SEqSetLhs sp b) (unS (vEqSet l (S a) b))
  (a            , Flex h sp    ) -> Flex   h (SEqSetRhs a sp)
  (a            , Unfold h sp b) -> Unfold h (SEqSetRhs a sp) (unS (vEqSet l a (S b)))
  (a            , b            ) -> Eq Set a b WBot

-- Terms
--------------------------------------------------------------------------------

vSp :: Lvl -> Val -> Spine -> Val
vSp l v sp = let
  go = vSp l v; {-# inline go #-}
  in case sp of
    SNil              -> v
    SApp sp t tu i    -> vApp (go sp) t tu i
    SProj1 sp         -> vProj1 (go sp)
    SProj2 sp         -> vProj2 (go sp)
    SProjField sp x n -> vProjField (go sp) x n
    SCoeSrc a b p t   -> vCoe l (go a) b p t
    SCoeTgt a b p t   -> vCoe l a (go b) p t
    SCoeComp a b p t  -> vCoeComp l a b p (go t)
    SEqType a t u     -> vEq l (go a) t u
    SEqSetLhs t u     -> vEqSet l (go t) u
    SEqSetRhs t u     -> vEqSet l t (go u)


eval :: Env -> Lvl -> S.Tm -> Val
eval env l t = let
  go = eval env l; {-# inline go #-}
  in case t of
    S.LocalVar x        -> vLocalVar env x
    S.TopDef x          -> vTopDef x
    S.Postulate x       -> Rigid (RHPostulate x) SNil
    S.Meta x            -> vMeta x
    S.Let _ _ _ t u     -> let t' = go t in eval (Snoc env (unS t')) (l + 1) u
    S.Pi x i a au b     -> Pi x i (go a) au (Close env l b)
    S.Sg x a au b bu    -> Sg x (go a) au (Close env l b) bu
    S.Lam x i a au t    -> Lam x i (go a) au (Close env l t)
    S.App t u uu i      -> vApp (go t) (go u) uu i
    S.Proj1 t           -> vProj1 (go t)
    S.Proj2 t           -> vProj2 (go t)
    S.ProjField t x n   -> vProjField (go t) x n
    S.Pair t tu u uu    -> Pair (go t) tu (go u) uu
    S.U u               -> U u
    S.Top               -> Top
    S.Tt                -> Tt
    S.Bot               -> Bot
    S.Eq a x y          -> vEq l (go a) (go x) (go y)
    S.Refl a t          -> Refl (go a) (go t)
    S.Coe a b p t       -> vCoe l (go a) (go b) (go p) (go t)
    S.Sym a x y p       -> Sym (go a) (go x) (go y) (go p)
    S.Trans a x y z p q -> Trans (go a) (go x) (go y) (go z) (go p) (go q)
    S.Ap a b f x y p    -> Ap (go a) (go b) (go f) (go x) (go y) (go p)
    S.Exfalso u a t     -> Exfalso u (go a) (go t)

-- Forcing
--------------------------------------------------------------------------------

forceUMax :: S.UMax -> S.U
forceUMax xs = S (IS.foldl' go S.WProp xs) where
  go = \u x -> runIO $ readUMeta (UMeta x) >>= \case
    UMEUnsolved  -> pure (unS (S u <> S.UVar (UMeta x)))
    UMESolved u' -> pure (unS (S u <> forceU u'))
  {-# inline go #-}
{-# noinline forceUMax #-}

forceU :: S.U -> S.U
forceU = \case
  S.UMax xs -> forceUMax xs
  u         -> u

-- | Force both flex and unfolding.
force :: Lvl -> Val -> Val
force l = \case
  Flex h sp    -> forceFlexHead l h sp
  Unfold _ _ v -> force' l (S v)
  v            -> v
{-# inline force #-}

force' :: Lvl -> Val -> Val
force' l = \case
  Flex h sp    -> forceFlexHead l h sp
  Unfold _ _ v -> force' l (S v)
  v            -> v

forceFlexHead :: Lvl -> FlexHead -> Spine -> Val
forceFlexHead l h sp = case h of
  FHMeta x -> S $ runIO $ readMeta x >>= \case
    MESolved v -> pure $ unS $ force' l (vSp l v sp)
    _          -> pure $ WFlex (FHMeta x) sp
  FHCoeRefl x a b p t -> S $ runIO $ readMeta x >>= \case
    MESolved v -> pure $ unS $ force' l (vCoeRefl l a b p t)
    _          -> pure $ WFlex (FHCoeRefl x a b p t) sp
  FHCoeUMax xs a b p t -> case forceUMax xs of
    S.Set     -> force' l (vSp l (vCoe l a b p t) sp)
    S.Prop    -> force' l (vSp l (vCoe l a b p t) sp)
    S.UMax xs -> Flex (FHCoeUMax xs a b p t) sp
  FHEqUMax xs a t u -> case forceUMax xs of
    S.Set     -> force' l (vSp l (vEq l a t u) sp)
    S.Prop    -> force' l (vSp l (vEq l a t u) sp)
    S.UMax xs -> Flex (FHEqUMax xs a t u) sp

-- | Force only flex.
fforce :: Lvl -> Val -> Val
fforce l = \case
  Flex h sp    -> fforceFlexHead l h sp
  v            -> v
{-# inline fforce #-}

fforce' :: Lvl -> Val -> Val
fforce' l = \case
  Flex h sp    -> fforceFlexHead l h sp
  v            -> v

fforceFlexHead :: Lvl -> FlexHead -> Spine -> Val
fforceFlexHead l h sp = case h of
  FHMeta x -> S $ runIO $ readMeta x >>= \case
    MESolved v -> pure $ WUnfold (UHMeta x) sp (unS (fforce' l (vSp l v sp)))
    _          -> pure $ WFlex (FHMeta x) sp
  FHCoeRefl x a b p t -> S $ runIO $ readMeta x >>= \case
    MESolved v -> pure $ unS $ fforce' l (vCoeRefl l a b p t)
    _          -> pure $ WFlex (FHCoeRefl x a b p t) sp
  FHCoeUMax xs a b p t -> case forceUMax xs of
    S.Set     -> fforce' l (vSp l (vCoe l a b p t) sp)
    S.Prop    -> fforce' l (vSp l (vCoe l a b p t) sp)
    S.UMax xs -> Flex (FHCoeUMax xs a b p t) sp
  FHEqUMax xs a t u -> case forceUMax xs of
    S.Set     -> fforce' l (vSp l (vEq l a t u) sp)
    S.Prop    -> fforce' l (vSp l (vEq l a t u) sp)
    S.UMax xs -> Flex (FHEqUMax xs a t u) sp


-- Conversion checking
--------------------------------------------------------------------------------

-- TODO: try to have small fix number of unfoldings in approximate mode. Benchmark.
-- Precondition: values have the same Set type (definitionally)
conv :: Lvl -> Val -> Val -> Ex
conv l t u = runIO ((ConvSame <$ convIO l DontUnfold t u) `catch` pure)
{-# inline conv #-}

convSpIO :: Lvl -> Unfolding -> Spine -> Spine -> IO ()
convSpIO l unfold sp sp' = let
  go   = convIO l unfold; {-# inline go #-}
  goSp = convSpIO l unfold; {-# inline goSp #-}

  goWithU un t t' = case forceU un of
    S.Prop -> pure ()
    _      -> go t t'
  {-# inline goWithU #-}

  goProjField :: Spine -> Spine -> Int -> IO ()
  goProjField sp          sp' 0 = goSp sp sp'
  goProjField (SProj2 sp) sp' n = goProjField sp sp' (n - 1)
  goProjField _           _   _ = throwIO ConvDiff

  in case Spine2 sp sp' of
    Spine2 (SNil             ) (SNil                ) -> pure ()
    Spine2 (SApp sp t u i    ) (SApp sp' t' u' i'   ) -> goSp sp sp' >> goWithU u t t'
    Spine2 (SProj1 sp        ) (SProj1 sp'          ) -> goSp sp sp'
    Spine2 (SProj2 sp        ) (SProj2 sp'          ) -> goSp sp sp'
    Spine2 (SProjField sp x n) (SProjField sp' x' n') -> goSp sp sp' >> unless (n == n) (throwIO ConvDiff)
    Spine2 (SProjField sp x n) (SProj1 sp'          ) -> goProjField sp' sp n
    Spine2 (SProj1 sp        ) (SProjField sp' x' n') -> goProjField sp sp' n'
    Spine2 (SCoeSrc a b p t  ) (SCoeSrc a' b' p' t' ) -> goSp a a' >> go b b' >> go t t'
    Spine2 (SCoeTgt a b p t  ) (SCoeTgt a' b' p' t' ) -> go a a' >> goSp b b' >> go t t'
    Spine2 (SCoeComp a b p t ) (SCoeComp a' b' p' t') -> go a a' >> go b b' >> goSp t t'
    Spine2 (SEqType a t u    ) (SEqType a' t' u'    ) -> goSp a a' >> go t t' >> go u u'
    Spine2 (SEqSetLhs t u    ) (SEqSetLhs t' u'     ) -> goSp t t' >> go u u'
    Spine2 (SEqSetRhs t u    ) (SEqSetRhs t' u'     ) -> go t t' >> goSp u u'
    _                                                 -> throwIO ConvDiff

convIO :: Lvl -> Unfolding -> Val -> Val -> IO ()
convIO l unfold t t' = let
  go   = convIO l unfold; {-# inline go #-}
  goSp = convSpIO l unfold; {-# inline goSp #-}

  goWithU un t t' = case forceU un of
    S.Prop -> pure ()
    _      -> go t t'
  {-# inline goWithU #-}

  force' t = case unfold of DoUnfold -> force l t
                            _        -> fforce l t
  {-# inline force' #-}

  cmpU :: S.U -> S.U -> IO ()
  cmpU u u' = case u of
    S.Set -> case u' of
      S.Set -> pure ()
      S.Prop -> throwIO ConvDiff
      S.UMax xs -> throwIO (ConvUMax xs)
    S.Prop -> case u' of
      S.Set -> throwIO ConvDiff
      S.Prop -> pure ()
      S.UMax xs -> throwIO (ConvUMax xs)
    S.UMax xs -> throwIO (ConvUMax xs)

  goUMax :: S.UMax -> S.UMax -> IO ()
  goUMax xs xs' = cmpU (forceUMax xs) (forceUMax xs')

  goU :: S.U -> S.U -> IO ()
  goU u u' = cmpU (forceU u) (forceU u')

  goUH :: UnfoldHead -> UnfoldHead -> IO ()
  goUH h h' = case (h, h') of
    (UHMeta x  , UHMeta x'  ) | x == x' -> pure ()
    (UHTopDef x, UHTopDef x') | x == x' -> pure ()
    _                                   -> throwIO ConvDiff
  {-# inline goUH #-}

  goMeta :: Meta -> Meta -> IO ()
  goMeta x x' = unless (x == x') (throwIO (ConvMeta x))
  {-# inline goMeta #-}

  goLvl :: Lvl -> Lvl -> IO ()
  goLvl x x' = unless (x == x') (throwIO ConvDiff)
  {-# inline goLvl #-}

  goFH :: FlexHead -> FlexHead -> IO ()
  goFH h h' = case (h, h') of
    (FHMeta x            , FHMeta x'                ) -> goMeta x x'
    (FHMeta x            , _                        ) -> throwIO (ConvMeta x)
    (FHCoeRefl x a b p t , FHCoeRefl x' a' b' p' t' ) -> goMeta x x' >> go a a' >> go b b' >> go t t'
    (FHCoeRefl x _ _ _ _ , _                        ) -> throwIO (ConvMeta x)
    (FHCoeUMax xs a b p t, FHCoeUMax xs' a' b' p' t') -> goUMax xs xs' >> go a a' >> go b b' >> go t t'
    (FHCoeUMax xs _ _ _ _, _                        ) -> throwIO (ConvUMax xs)
    (FHEqUMax xs a t u   , FHEqUMax xs' a' t' u'    ) -> goUMax xs xs' >> go a a' >> go t t' >> go u u'
    (FHEqUMax xs a t u   , _                        ) -> throwIO (ConvUMax xs)

  -- Note the "impossible": relevant computation never blocks on equality proofs, and
  -- conversion checking never looks at irrelevant values. Hence, every equation-headed
  -- neutral must be irrelevant, which contradicts the relevance assumption.
  goRH :: RigidHead -> RigidHead -> IO ()
  goRH h h' = case (h, h') of
    (RHLocalVar x    , RHLocalVar x'      ) -> goLvl x x'
    (RHPostulate x   , RHPostulate x'     ) -> goLvl x x'
    (RHRefl{}        , RHRefl{}           ) -> impossible
    (RHSym{}         , RHSym{}            ) -> impossible
    (RHAp{}          , RHAp{}             ) -> impossible
    (RHTrans{}       , RHTrans{}          ) -> impossible
    (RHExfalso u a t , RHExfalso u' a' t' ) -> goU u u' >> go a a'
    (RHCoe a b p t   , RHCoe a' b' p' t'  ) -> go a a' >> go b b' >> go t t'
    _                                       -> throwIO ConvDiff

  fhBlocker :: FlexHead -> Ex
  fhBlocker = \case
    FHMeta x             -> ConvMeta x
    FHCoeRefl x _ _ _ _  -> ConvMeta x
    FHCoeUMax xs _ _ _ _ -> ConvUMax xs
    FHEqUMax xs _ _ _    -> ConvUMax xs
  {-# inline fhBlocker #-}

  in case Val2 (force' t) (force' t') of
    Val2 (Eq _ _ _ t    ) (t'                ) -> go (S t) t'
    Val2 (t             ) (Eq _ _ _ t'       ) -> go t (S t')
    Val2 (Unfold h sp t ) (Unfold h' sp' t'  ) -> (goUH h h' >> goSp sp sp' >> go (S t) (S t'))
                                                  `catch` (\_ -> convIO l DoUnfold (S t) (S t'))
    Val2 (Unfold h sp t ) (t'                ) -> convIO l DoUnfold (S t) t'
    Val2 (t             ) (Unfold h' sp' t'  ) -> convIO l DoUnfold t (S t')
    Val2 (Pi _ i a au b ) (Pi _ i' a' au' b' ) -> goU au au' >> go a a' >>
                                                  convIO (l + 1) unfold (b $$ Var l) (b' $$ Var l)
    Val2 (Sg _ a au b bu) (Sg _ a' au' b' bu') -> goU au au' >> goU bu bu' >> go a a' >>
                                                  convIO (l + 1) unfold (b $$ Var l) (b' $$ Var l)
    Val2 (Lam _ _ _ _ t ) (Lam _ _ _ _ t'    ) -> convIO (l + 1) unfold (t $$ Var l) (t' $$ Var l)
    Val2 (Lam _ i _ u t ) (t'                ) -> convIO (l + 1) unfold (t $$ Var l) (vApp t' (Var l) u i)
    Val2 (t             ) (Lam _ i' _ u' t'  ) -> convIO (l + 1) unfold (vApp t (Var l) u' i') (t' $$ Var l)
    Val2 (Pair t tu u uu) (Pair t' tu' u' uu') -> goWithU tu t t' >> goWithU uu u u'
    Val2 (Pair t tu u uu) (t'                ) -> goWithU tu t (vProj1 t') >> goWithU uu u (vProj2 t')
    Val2 (t             ) (Pair t' tu' u' uu') -> goWithU tu' (vProj1 t) t' >> goWithU uu' (vProj2 t) u'
    Val2 (U u           ) (U u'              ) -> goU u u'
    Val2 (Top           ) (Top               ) -> pure ()
    Val2 (Tt            ) (Tt                ) -> pure ()
    Val2 (Bot           ) (Bot               ) -> pure ()
    Val2 (Rigid h sp    ) (Rigid h' sp'      ) -> goRH h h' >> goSp sp sp'
    Val2 (Flex h sp     ) (Flex h' sp'       ) -> goFH h h' >> goSp sp sp'
    Val2 (Flex h sp     ) (t'                ) -> throwIO (fhBlocker h)
    Val2 (t             ) (Flex h' sp'       ) -> throwIO (fhBlocker h')
    Val2 (_             ) (_                 ) -> throwIO ConvDiff


-- Quoting
--------------------------------------------------------------------------------

quoteSp :: Lvl -> Unfolding -> S.Tm -> Spine -> S.Tm
quoteSp l unfold h sp = let
  go   = quote l unfold;     {-# inline go #-}
  goSp = quoteSp l unfold h; {-# inline goSp #-}
  in case sp of
    SNil              -> h
    SApp sp t tu i    -> S.App (goSp sp) (go t) tu i
    SProj1 sp         -> S.Proj1 (goSp sp)
    SProj2 sp         -> S.Proj2 (goSp sp)
    SProjField sp x n -> S.ProjField (goSp sp) x n
    SCoeSrc a b p t   -> S.Coe (goSp a) (go b) (go p) (go t)
    SCoeTgt a b p t   -> S.Coe (go a) (goSp b) (go p) (go t)
    SCoeComp a b p t  -> S.Coe (go a) (go b) (go p) (goSp t)
    SEqType a t u     -> S.Eq (goSp a) (go t) (go u)
    SEqSetLhs t u     -> S.Eq (S.U S.Set) (goSp t) (go u)
    SEqSetRhs t u     -> S.Eq (S.U S.Set) (go t) (goSp u)

quote :: Lvl -> Unfolding -> Val -> S.Tm
quote l unfold v = let
  go       = quote l unfold;   {-# inline go #-}
  goSp     = quoteSp l unfold; {-# inline goSp #-}
  force' v = case unfold of DoUnfold -> force l v; _ -> fforce l v

  goRH :: RigidHead -> S.Tm
  goRH = \case
    RHLocalVar x        -> S.LocalVar (lvlToIx l x)
    RHPostulate x       -> S.Postulate x
    RHRefl a t          -> S.Refl (go a) (go t)
    RHSym a t u p       -> S.Sym (go a) (go t) (go u) (go p)
    RHAp a b f t u p    -> S.Ap (go a) (go b) (go f) (go t) (go u) (go p)
    RHTrans a t u v p q -> S.Trans (go a) (go t) (go u) (go v) (go p) (go q)
    RHExfalso u a t     -> S.Exfalso u (go a) (go t)
    RHCoe a b p t       -> S.Coe (go a) (go b) (go p) (go t)

  goFH :: FlexHead -> S.Tm
  goFH = \case
    FHMeta x            -> S.Meta x
    -- TODO: consider adding this to syntax, so that we can skip expensive re-conversion checks
    FHCoeRefl _ a b p t -> S.Coe (go a) (go b) (go p) (go t)
    FHCoeUMax _ a b p t -> S.Coe (go a) (go b) (go p) (go t)
    FHEqUMax _ a t u    -> S.Eq (go a) (go t) (go u)

  goUH :: UnfoldHead -> S.Tm
  goUH = \case
    UHMeta x   -> S.Meta x
    UHTopDef x -> S.TopDef x

  goCl :: Closure -> S.Tm
  goCl t = quote (l + 1) unfold (t $$ Var l)
  {-# inline goCl #-}

  in case force' v of
    Rigid h sp     -> goSp (goRH h) sp
    Flex h sp      -> goSp (goFH h) sp
    Unfold h sp _  -> goSp (goUH h) sp
    Eq a t u _     -> S.Eq (go a) (go t) (go u)
    U u            -> S.U u
    Top            -> S.Top
    Tt             -> S.Tt
    Bot            -> S.Bot
    Pair t tu u uu -> S.Pair (go t) tu (go u) uu
    Sg x a au b bu -> S.Sg x (go a) au (goCl b) bu
    Pi x i a au b  -> S.Pi x i (go a) au (goCl b)
    Lam x i a au t -> S.Lam x i (go a) au (goCl t)
