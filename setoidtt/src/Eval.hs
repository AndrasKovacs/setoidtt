
module Eval (
    ($$), vApp, vProj1, vProj2, vProjField
  , vCoe, vEq, forceU, conv, force, fforce, vSp, vCoeP, eval
  ) where

import Control.Monad
import IO
import qualified Data.IntSet as IS

import Common
import ElabState
import Syntax (U(..), Tm, pattern Prop, pattern UVar, type UMax)
import Value
import qualified Syntax as S
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


-- Variables
--------------------------------------------------------------------------------

vLocalVar :: Env -> Ix -> Val
vLocalVar (EDef _ v)   0 = v
vLocalVar (EDef env _) x = vLocalVar env (x - 1)
vLocalVar _ _            = impossible

vMeta :: Meta -> Val
vMeta x = case runIO (readMeta x) of
  MEUnsolved{} -> Flex (FHMeta x) SNil
  MESolved v   -> Unfold (UHMeta x) SNil v
{-# inline vMeta #-}

vTopDef :: Lvl -> Val
vTopDef x = case runIO (readTop x) of
  TEDef v _ _ _ _ -> Unfold (UHTopDef x) SNil v
  _               -> impossible
{-# inline vTopDef #-}

-- Functions
--------------------------------------------------------------------------------

infixl 2 $$
($$) :: Closure -> Val -> Val
($$) cl u = case cl of
  CFun t         -> t u
  CClose env l t -> eval (EDef env u) l t
{-# inline ($$) #-}

vApp :: Val -> Val -> U -> Icit -> Val
vApp t u un i = case t of
  Lam _ _ _ _ t -> t $$ u
  Rigid h sp    -> Rigid  h (SApp sp u un i)
  Flex h sp     -> Flex   h (SApp sp u un i)
  Unfold h sp t -> Unfold h (SApp sp u un i) (vApp t u un i)
  _             -> impossible

-- Projections
--------------------------------------------------------------------------------

vProj1 :: Val -> Val
vProj1 t = case t of
  Pair t _ u _  -> t
  Rigid h sp    -> Rigid  h (SProj1 sp)
  Flex h sp     -> Flex   h (SProj1 sp)
  Unfold h sp t -> Unfold h (SProj1 sp) (vProj1 t)
  _             -> impossible

vProj2 :: Val -> Val
vProj2 t = case t of
  Pair t _ u _  -> u
  Rigid h sp    -> Rigid  h (SProj2 sp)
  Flex h sp     -> Flex   h (SProj2 sp)
  Unfold h sp t -> Unfold h (SProj2 sp) (vProj2 t)
  _             -> impossible

vProjField :: Val -> Name -> Int -> Val
vProjField t ~x n = case t of
  Pair t tu u uu -> case n of 0 -> t
                              n -> vProjField u x (n - 1)
  Rigid h sp     -> Rigid  h (SProjField sp x n)
  Flex h sp      -> Flex   h (SProjField sp x n)
  Unfold h sp t  -> Unfold h (SProjField sp x n) (vProjField t x n)
  _              -> impossible

-- Universe matching
--------------------------------------------------------------------------------

data MatchU = MUProp | MUSet | MUDiff | MUUMax IS.IntSet

matchUMaxSet :: UMax -> MatchU
matchUMaxSet xs = case forceUMax xs of
  Set     -> MUSet
  Prop    -> MUDiff
  UMax xs -> MUUMax xs
{-# noinline matchUMaxSet #-}

matchUMaxProp :: UMax -> MatchU
matchUMaxProp xs = case forceUMax xs of
  Set     -> MUDiff
  Prop    -> MUProp
  UMax xs -> MUUMax xs
{-# noinline matchUMaxProp #-}

matchUMax :: UMax -> U -> MatchU
matchUMax xs u = case forceUMax xs of
  Set -> case u of
    Set      -> MUSet
    Prop     -> MUDiff
    UMax xs' -> matchUMaxSet xs'
  Prop -> case u of
    Set      -> MUDiff
    Prop     -> MUProp
    UMax xs' -> matchUMaxProp xs'
  UMax xs -> MUUMax xs
{-# noinline matchUMax #-}

-- | Match universes, but don't check equality of neutrals, instead immediately
--  flexibly fail on any UMax. We need this kind of comparison in evaluation,
--  because computation cannot progress in the presence of UMax. The elaborate
--  implementation serves to reduce code bloat in vEq and vCoe (halves code size!)
matchU :: U -> U -> MatchU
matchU u u' = case u of
  Set -> case u' of
    Set      -> MUSet
    Prop     -> MUDiff
    UMax xs' -> matchUMaxSet xs'
  Prop -> case u' of
    Set      -> MUDiff
    Prop     -> MUProp
    UMax xs' -> matchUMaxProp xs'
  UMax xs -> matchUMax xs u'


-- Coercion
--------------------------------------------------------------------------------

vCoe :: Lvl -> Val -> Val -> Val -> Val -> Val
vCoe l a b ~p t = case (a, b) of
  (topA@(Pi x i a au b), topB@(Pi x' i' a' au' b'))
    | i /= i'   -> Exfalso Set (Pi x' i' a' au' b') p
    | otherwise -> case matchU au au' of
        MUSet     -> Lam (pick x x') i a' Set $ CFun \ ~a1 ->
                     let p1 = vProj1 p
                         p2 = vProj2 p
                         a0 = vCoe l a' a (Sym VSet a a' p1) a1
                     in vCoe l (b $$ a0) (b' $$ a1) (vApp p2 a0 Set Expl) (vApp t a0 Set i)
        MUProp    -> Lam (pick x x') i a' Prop $ CFun \ ~a1 ->
                     let p1 = vProj1 p
                         p2 = vProj2 p
                         a0 = vCoeP (Sym VProp a a' p1) a1
                     in vCoe l (b $$ a0) (b' $$ a1) (vApp p2 a0 Prop Expl) (vApp t a0 Prop i)
        MUDiff    -> Exfalso Set topB p
        MUUMax au -> Flex (FHCoeUMax au topA topB p t) SNil

  (topA@(Sg x a au b bu), topB@(Sg x' a' au' b' bu')) ->
    case (matchU au au', matchU bu bu') of
      (MUSet, MUSet)   -> let p1  = vProj1 t
                              p2  = vProj2 t
                              p1' = vCoe l a a' (vProj1 p) p1
                              p2' = vCoe l (b $$ p1) (b' $$ p1') (vProj2 p) p2
                          in Pair p1' Set p2' Set
      (MUSet, MUProp)  -> let p1  = vProj1 t
                              p2  = vProj2 t
                              p1' = vCoe l a a' (vProj1 p) p1
                              p2' = vCoeP (vProj2 p) p2
                          in Pair p1' Set p2' Prop
      (MUProp, MUSet)  -> let p1  = vProj1 t
                              p2  = vProj2 t
                              p1' = vCoeP (vProj1 p) p1
                              p2' = vCoe l (b $$ p1) (b' $$ p1') (vProj2 p) p2
                          in Pair p1' Prop p2' Set
      (MUProp, MUProp) -> impossible
      (MUDiff, _)      -> Exfalso Set topB p
      (_ , MUDiff)     -> Exfalso Set topB p
      (MUUMax au, _)   -> Flex (FHCoeUMax au topA topB p t) SNil
      (_, MUUMax bu)   -> Flex (FHCoeUMax bu topA topB p t) SNil

  (Flex h sp    , b            ) -> Flex h (SCoeSrc sp b p t)
  (Unfold h sp a, b            ) -> Unfold h (SCoeSrc sp b p t) (vCoe l a b p t)
  (a            , Flex h sp    ) -> Flex h (SCoeTgt a sp p t)
  (a            , Unfold h sp b) -> Unfold h (SCoeTgt a sp p t) (vCoe l a b p t)
  (a            , b            ) -> vCoeComp l a b p t

-- | Try to compute coercion composition.
vCoeComp :: Lvl -> Val -> Val -> Val -> Val -> Val
vCoeComp l a b p t = case t of
  Flex h sp                     -> Flex h (SCoeComp a b p sp)
  Unfold h sp t                 -> Unfold h (SCoeComp a b p sp) (vCoeComp l a b p t)
  Rigid (RHCoe a' _ p' t') SNil -> vCoeRefl l a' b (Trans VSet a' a b p' p) t'
  t                             -> vCoeRefl l a b p t

-- | Try to compute reflexive coercion.
vCoeRefl :: Lvl -> Val -> Val -> Val -> Val -> Val
vCoeRefl l a b p t = case conv l a b of
  ConvSame    -> t
  ConvDiff    -> Rigid (RHCoe a b p t) SNil
  ConvMeta x  -> Flex (FHCoeRefl x a b p t) SNil
  ConvUMax xs -> Flex (FHCoeUMax xs a b p t) SNil

-- | coeP : {A B : Prop} -> A = B -> A -> B
vCoeP :: Val -> Val -> Val
vCoeP p t = vApp (vProj1 p) t Prop Expl
{-# inline vCoeP #-}


-- Equality type
--------------------------------------------------------------------------------

vEq :: Lvl -> Val -> Val -> Val -> Val
vEq l a t u = case a of
  U un -> case forceU un of
    Set     -> vEqSet l t u
    Prop    -> vEqProp t u
    UMax xs -> Flex (FHEqUMax xs a t u) SNil

  -- funext always computes to Expl function
  topA@(Pi x i a au b) -> Eq topA t u $
    Pi x Expl a au $ CFun \ ~x -> vEq l (b $$ x) (vApp t x au i) (vApp u x au i)

  -- equality of Prop fields is automatically skipped
  topA@(Sg x a (forceU -> !au) b (forceU -> !bu)) ->
    let p1t = vProj1 t
        p1u = vProj1 u
        p2t = vProj2 t
        p2u = vProj2 u in
    case (au, bu) of
      (Set, Prop)  -> vEq l a p1t p1u
      (Set, Set )  -> Eq topA t u $
                        PiEP NP (vEq l a p1t p1u) \ ~p ->
                        vEq l (b $$ p1u)
                              (vCoe l (b $$ p1t) (b $$ p1u)
                                      (Ap a VSet (Lam x Expl a Set b) p1t p1u p) p2t)
                              p2u
      (Prop, Set)  -> vEq l (b $$ p1t) p2t p2u
      (Prop, Prop) -> impossible
      (UMax xs, _) -> Flex (FHEqUMax xs topA t u) SNil
      (_, UMax xs) -> Flex (FHEqUMax xs topA t u) SNil

  Rigid  h sp   -> Rigid  h (SEqType sp t u)
  Flex   h sp   -> Flex   h (SEqType sp t u)
  Unfold h sp a -> Unfold h (SEqType sp t u) (vEq l a t u)
  _             -> impossible

vEqProp :: Val -> Val -> Val
vEqProp a b = Eq VProp a b (vAnd (vImpl a b) (vImpl b a))
{-# inline vEqProp #-}

-- | Equality of sets.
vEqSet :: Lvl -> Val -> Val -> Val
vEqSet l a b = case (a, b) of
  (U u, U u') -> case matchU u u' of
    MUProp     -> Eq VSet VProp VProp Top
    MUSet      -> Eq VSet VSet VSet Top
    MUDiff     -> Eq VSet (U u) (U u') Bot
    MUUMax xs  -> Flex (FHEqUMax xs VSet (U u) (U u')) SNil

  (topA@(Pi x i a au b), topB@(Pi x' i' a' au' b')) ->
    let eq = Eq VSet topA topB in
    case matchU au au' of
      MUProp      -> eq $ SgPP NP (vEqProp a a') \ ~p →
                     PiEP (pick x x') a \ ~x -> vEqSet l (b $$ x) (b' $$ vCoeP p x)
      MUSet       -> eq $ SgPP NP (vEqSet l a a') \ ~p →
                     PiEP (pick x x') a \ ~x -> vEqSet l (b $$ x) (b' $$ vCoe l a a' p x)
      MUDiff      -> eq Bot
      MUUMax au   -> Flex (FHEqUMax au VSet topA topB) SNil

  (topA@(Sg x a au b bu), topB@(Sg x' a' au' b' bu')) ->
    let eq = Eq VSet topA topB in
    case (matchU au au', matchU bu bu') of
      (MUSet,  MUSet )  -> eq $ SgPP NP (vEqSet l a a') \ ~p ->
                           PiEP (pick x x') a \ ~x -> vEqSet l (b $$ x) (b' $$ vCoe l a a' p x)
      (MUSet,  MUProp)  -> eq $ SgPP NP (vEqSet l a a') \ ~p ->
                           PiEP (pick x x') a \ ~x -> vEqProp (b $$ x) (b' $$ vCoeP p x)
      (MUProp, MUSet )  -> eq $ SgPP NP (vEqProp a a') \ ~p ->
                           PiEP (pick x x') a \ ~x -> vEqSet l (b $$ x) (b' $$ vCoe l a a' p x)
      (MUProp, MUProp)  -> impossible
      (MUDiff, _    )   -> eq Bot
      (_    , MUDiff)   -> eq Bot
      (MUUMax au, _)    -> Flex (FHEqUMax au VSet topA topB) SNil
      (_, MUUMax bu)    -> Flex (FHEqUMax bu VSet topA topB) SNil

  (Flex h sp    , b            ) -> Flex   h (SEqSetLhs sp b)
  (Unfold h sp a, b            ) -> Unfold h (SEqSetLhs sp b) (vEqSet l a b)
  (a            , Flex h sp    ) -> Flex   h (SEqSetRhs a sp)
  (a            , Unfold h sp b) -> Unfold h (SEqSetRhs a sp) (vEqSet l a b)
  (a            , b            ) -> Eq VSet a b Bot

-- Terms
--------------------------------------------------------------------------------

vSp :: Lvl -> Val -> Spine -> Val
vSp l ~v = go where
  go SNil                        = v
  go (SApp sp t tu i)            = vApp (go sp) t tu i

  go (SProj1 sp)                 = vProj1 (go sp)
  go (SProj2 sp)                 = vProj2 (go sp)
  go (SProjField sp x n)         = vProjField (go sp) x n

  go (SCoeSrc (go -> !a) b p t)  = vCoe l a b p t
  go (SCoeTgt a (go -> !b) p t)  = vCoe l a b p t
  go (SCoeComp a b p (go -> !t)) = vCoeComp l a b p t

  go (SEqType a t u)             = vEq l (go a) t u
  go (SEqSetLhs (go -> !t) u)    = vEqSet l t u
  go (SEqSetRhs t (go -> !u))    = vEqSet l t u

eval :: Env -> Lvl -> Tm -> Val
eval env l = go where
  go = \case
    S.LocalVar x        -> vLocalVar env x
    S.TopDef x          -> vTopDef x
    S.Postulate x       -> Rigid (RHPostulate x) SNil
    S.MetaVar x         -> vMeta x
    S.Let _ _ _ t u     -> let t' = go t in eval (EDef env t') (l + 1) u
    S.Pi x i a au b     -> Pi x i (go a) au (CClose env l b)
    S.Sg x a au b bu    -> Sg x (go a) au (CClose env l b) bu
    S.Lam x i a au t    -> Lam x i (go a) au (CClose env l t)
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

forceUMax :: UMax -> U
forceUMax xs = IS.foldl' go Prop xs where
  go u x = u <> maybe (UVar (UMeta x)) forceU (runIO (readUMeta (UMeta x)))
  {-# inline go #-}
{-# noinline forceUMax #-}

forceU :: U -> U
forceU = \case
  UMax xs -> forceUMax xs
  u       -> u
-- {-# noinline forceU #-}

-- | Force both flex and unfolding.
force :: Lvl -> Val -> Val
force l = \case
  Flex h sp    -> forceFlexHead l h sp
  Unfold _ _ v -> force l v
  v            -> v

forceFlexHead :: Lvl -> FlexHead -> Spine -> Val
forceFlexHead l h sp = case h of
  FHMeta x -> case runIO (readMeta x) of
    MESolved v -> force l $! vSp l v sp
    _          -> Flex (FHMeta x) sp
  FHCoeRefl x a b p t -> case runIO (readMeta x) of
    MESolved v -> force l (vCoeRefl l a b p t)
    _          -> Flex (FHCoeRefl x a b p t) sp
  FHCoeUMax xs a b p t -> case forceUMax xs of
    Set     -> force l ((vSp l $! vCoe l a b p t) sp)
    Prop    -> force l ((vSp l $! vCoe l a b p t) sp)
    UMax xs -> Flex (FHCoeUMax xs a b p t) sp
  FHEqUMax xs a t u -> case forceUMax xs of
    Set     -> force l ((vSp l $! vEq l a t u) sp)
    Prop    -> force l ((vSp l $! vEq l a t u) sp)
    UMax xs -> Flex (FHEqUMax xs a t u) sp

-- | Force only flex.
fforce :: Lvl -> Val -> Val
fforce l = \case
  Flex h sp    -> fforceFlexHead l h sp
  v            -> v

fforceFlexHead :: Lvl -> FlexHead -> Spine -> Val
fforceFlexHead l h ~sp = case h of
  FHMeta x -> case runIO (readMeta x) of
    MESolved v -> Unfold (UHMeta x) sp (fforce l $! vSp l v sp)
    _          -> Flex (FHMeta x) sp
  FHCoeRefl x a b p t -> case runIO (readMeta x) of
    MESolved v -> fforce l (vCoeRefl l a b p t)
    _          -> Flex (FHCoeRefl x a b p t) sp
  FHCoeUMax xs a b p t -> case forceUMax xs of
    Set     -> fforce l ((vSp l $! vCoe l a b p t) sp)
    Prop    -> fforce l ((vSp l $! vCoe l a b p t) sp)
    UMax xs -> Flex (FHCoeUMax xs a b p t) sp
  FHEqUMax xs a t u -> case forceUMax xs of
    Set     -> fforce l ((vSp l $! vEq l a t u) sp)
    Prop    -> fforce l ((vSp l $! vEq l a t u) sp)
    UMax xs -> Flex (FHEqUMax xs a t u) sp


-- Conversion checking
--------------------------------------------------------------------------------

-- | Precondition: values have the same Set type (definitionally)
conv :: Lvl -> Val -> Val -> Ex
conv l t u = runIO ((ConvSame <$ convIO l False t u) `catch` pure)
{-# inline conv #-}

convIO :: Lvl -> Bool -> Val -> Val -> IO ()
convIO l unfold = go where

  force' t | unfold    = force l t
           | otherwise = fforce l t
  {-# inline force' #-}

  goUMax :: UMax -> UMax -> IO ()
  goUMax xs xs' = case (forceUMax xs, forceUMax xs') of
    (Set     , Set      ) -> pure ()
    (Prop    , Prop     ) -> pure ()
    (UMax xs , UMax xs' ) -> unless (xs == xs') (throwIO (ConvUMax xs))
    (UMax xs , _        ) -> throwIO (ConvUMax xs)
    (_       , UMax xs' ) -> throwIO (ConvUMax xs')
    (_       , _        ) -> throwIO ConvDiff

  goU :: U -> U -> IO ()
  goU u u' = case (forceU u, forceU u') of
    (Set     , Set      ) -> pure ()
    (Prop    , Prop     ) -> pure ()
    (UMax xs , UMax xs' ) -> unless (xs == xs') (throwIO (ConvUMax xs))
    (UMax xs , _        ) -> throwIO (ConvUMax xs)
    (_       , UMax xs' ) -> throwIO (ConvUMax xs')
    (_       , _        ) -> throwIO ConvDiff

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

  goProjField :: Spine -> Spine -> Int -> IO ()
  goProjField sp sp' n = case (sp, n) of
    (sp,        0) -> goSp sp sp'
    (SProj2 sp, n) -> goProjField sp sp' (n - 1)
    _              -> throwIO ConvDiff

  goSp :: Spine -> Spine -> IO ()
  goSp sp sp' = case (sp, sp') of
    (SNil              , SNil                ) -> pure ()
    (SApp sp t u i     , SApp sp' t' u' i'   ) -> goSp sp sp' >> goWithU u t t'
    (SProj1 sp         , SProj1 sp'          ) -> goSp sp sp'
    (SProj2 sp         , SProj2 sp'          ) -> goSp sp sp'
    (SProjField sp x n , SProjField sp' x' n') -> goSp sp sp' >> unless (n == n) (throwIO ConvDiff)
    (SProjField sp x n , SProj1 sp'          ) -> goProjField sp' sp n
    (SProj1 sp         , SProjField sp' x' n') -> goProjField sp sp' n'
    (SCoeSrc a b p t   , SCoeSrc a' b' p' t' ) -> goSp a a' >> go b b' >> go t t'
    (SCoeTgt a b p t   , SCoeTgt a' b' p' t' ) -> go a a' >> goSp b b' >> go t t'
    (SCoeComp a b p t  , SCoeComp a' b' p' t') -> go a a' >> go b b' >> goSp t t'
    (SEqType a t u     , SEqType a' t' u'    ) -> goSp a a' >> go t t' >> go u u'
    (SEqSetLhs t u     , SEqSetLhs t' u'     ) -> goSp t t' >> go u u'
    (SEqSetRhs t u     , SEqSetRhs t' u'     ) -> go t t' >> goSp u u'
    _                                          -> throwIO ConvDiff

  goWithU :: U -> Val -> Val -> IO ()
  goWithU un ~t ~t' = case forceU un of
    Prop -> pure ()
    _    -> go t t'
  {-# inline goWithU #-}

  fhBlocker :: FlexHead -> Ex
  fhBlocker = \case
    FHMeta x             -> ConvMeta x
    FHCoeRefl x _ _ _ _  -> ConvMeta x
    FHCoeUMax xs _ _ _ _ -> ConvUMax xs
    FHEqUMax xs _ _ _    -> ConvUMax xs
  {-# inline fhBlocker #-}

  -- Precondition: values must have the same type (definitionally)
  go :: Val -> Val -> IO ()
  go t t' = case (force' t, force' t') of
    (Eq _ _ _ t    , t'                ) -> go t t'
    (t             , Eq _ _ _ t'       ) -> go t t'

    (Unfold h sp t , Unfold h' sp' t'  ) -> (goUH h h' >> goSp sp sp' >> go t t')
                                            `catch` (\_ -> convIO l True t t')

    (Unfold h sp t , t'                ) -> convIO l True t t'
    (t             , Unfold h' sp' t'  ) -> convIO l True t t'

    (Pi _ i a au b , Pi _ i' a' au' b' ) -> goU au au' >> go a a' >>
                                            convIO (l + 1) unfold (b $$ VVar l) (b' $$ VVar l)

    (Sg _ a au b bu, Sg _ a' au' b' bu') -> goU au au' >> goU bu bu' >> go a a' >>
                                            convIO (l + 1) unfold (b $$ VVar l) (b' $$ VVar l)

    (Lam _ _ _ _ t , Lam _ _ _ _ t'    ) -> convIO (l + 1) unfold (t $$ VVar l) (t' $$ VVar l)
    (Lam _ i _ u t , t'                ) -> convIO (l + 1) unfold (t $$ VVar l) (vApp t' (VVar l) u i)
    (t             , Lam _ i' _ u' t'  ) -> convIO (l + 1) unfold (vApp t (VVar l) u' i') (t' $$ VVar l)

    (Pair t tu u uu, Pair t' tu' u' uu') -> goWithU tu t t' >> goWithU uu u u'
    (Pair t tu u uu, t'                ) -> goWithU tu t (vProj1 t') >> goWithU uu u (vProj2 t')
    (t             , Pair t' tu' u' uu') -> goWithU tu' (vProj1 t) t' >> goWithU uu' (vProj2 t) u'

    (U u           , U u'              ) -> goU u u'
    (Top           , Top               ) -> pure ()
    (Tt            , Tt                ) -> pure ()
    (Bot           , Bot               ) -> pure ()
    (Rigid h sp    , Rigid h' sp'      ) -> goRH h h' >> goSp sp sp'

    (Flex h sp     , Flex h' sp'       ) -> goFH h h' >> goSp sp sp'
    (Flex h sp     , t'                ) -> throwIO (fhBlocker h)
    (t             , Flex h' sp'       ) -> throwIO (fhBlocker h')
    (_             , _                 ) -> throwIO ConvDiff
