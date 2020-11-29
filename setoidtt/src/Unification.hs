
module Unification where

import Control.Monad
import qualified Data.Array.Dynamic.L as D
import qualified Data.IntMap as IM

import Common
import Cxt
import ElabState
import Evaluation
import Exceptions
import Values
import qualified EvalInCxt
import qualified Syntax as S

--------------------------------------------------------------------------------

closeType :: S.Locals -> S.Ty -> S.Ty
closeType ls topA = case ls of
  S.Empty              -> topA
  S.Define ls x t a au -> closeType ls (S.Let x a au t topA)
  S.Bind ls x a au     -> closeType ls (S.Pi x Expl a au topA)

freshMeta :: Cxt -> WTy -> S.U -> IO S.Tm
freshMeta cxt ~va au = S <$> wfreshMeta cxt va au; {-# inline freshMeta #-}
wfreshMeta :: Cxt -> WTy -> S.U -> IO S.WTm
wfreshMeta cxt ~va au = do
  wfreshMeta' cxt (EvalInCxt.quote cxt (S va)) au
{-# inlinable wfreshMeta #-}

freshMeta' :: Cxt -> S.Ty -> S.U -> IO S.Tm
freshMeta' cxt a au = S <$> wfreshMeta' cxt a au; {-# inline freshMeta' #-}
wfreshMeta' :: Cxt -> S.Ty -> S.U -> IO S.WTm
wfreshMeta' cxt a au = do
  let va = eval Nil 0 (closeType (_locals cxt) a)
  m <- newMeta va au
  pure $ S.WInsertedMeta m (_locals cxt)
{-# inlinable wfreshMeta' #-}

freshTyInU :: Cxt -> S.U -> IO S.Ty
freshTyInU cxt u = S <$> wfreshTyInU cxt u; {-# inline freshTyInU #-};
wfreshTyInU :: Cxt -> S.U -> IO S.WTy
wfreshTyInU cxt u = wfreshMeta cxt (WU u) S.Set
{-# inlinable wfreshTyInU #-}


-- Solutions
--------------------------------------------------------------------------------

solveU :: ConvState -> UMetaVar -> S.U -> IO ()
solveU CSFlex _ _ = throwIO CantUnify
solveU _      x u = do
  D.modify' uCxt (coerce x) \case
    UMEUnsolved -> UMESolved u
    UMESolved{} -> impossible
{-# inline solveU #-}

data PartialRenaming = PRen {
    dom :: Lvl
  , cod :: Lvl
  , ren :: IM.IntMap Lvl}

lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (coerce cod) dom ren)

invert :: Lvl -> Spine -> IO PartialRenaming
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)  -- TODO: this is not unboxed! Pass RW instead
      go SNil = pure (0, mempty)
      go (SApp sp t u i) = do
        (dom, ren) <- go sp
        case forceFU gamma t of
          Var (Lvl x) | IM.notMember x ren ->
            pure ((,) $$! (dom + 1) $$! (IM.insert x dom ren))
          _ ->
            throwIO CantUnify
      go _ = do
        throwIO CantUnify

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

renameSp :: MetaVar -> ConvState -> PartialRenaming -> S.Tm -> Spine -> IO S.Tm
renameSp m st pren t sp = S <$> wrenameSp m st pren t sp; {-# inline renameSp #-}
wrenameSp :: MetaVar -> ConvState -> PartialRenaming -> S.Tm -> Spine -> IO S.WTm
wrenameSp m st pren t sp = let
  go   t  = rename m st pren t;      {-# inline go #-}
  goSp sp = renameSp m st pren t sp; {-# inline goSp #-}
  in case sp of
    SNil             -> pure $! unS t
    SApp t u uu i    -> S.WApp <$> goSp t <*> go u <*> pure uu <*> pure i
    SProj1 t         -> S.WProj1 <$> goSp t
    SProj2 t         -> S.WProj2 <$> goSp t
    SProjField t x n -> S.WProjField <$> goSp t <*> pure x <*> pure n
    SCoeSrc a b p t  -> S.WCoe <$> goSp a <*> go b <*> go p <*> go t
    SCoeTgt a b p t  -> S.WCoe <$> go a <*> goSp b <*> go p <*> go t
    SCoeComp a b p t -> S.WCoe <$> go a <*> go b <*> go p <*> goSp t
    SEqType a t u    -> S.WEq <$> goSp a <*> go t <*> go u
    SEqSetLhs t u    -> S.WEq (S.U S.Set) <$> goSp t <*> go u
    SEqSetRhs t u    -> S.WEq (S.U S.Set) <$> go t <*> goSp u


rename :: MetaVar -> ConvState -> PartialRenaming -> Val -> IO S.Tm
rename m st pren v = S <$> wrename m st pren v; {-# inline rename #-}
wrename m st pren v = let
  go     t = rename m st pren t;                            {-# inline go #-}
  goBind t = rename m st (lift pren) (t $$ Var (cod pren)); {-# inline goBind #-}
  force t  = case st of CSFull -> forceFU (cod pren) t
                        _      -> forceF  (cod pren) t
  {-# inline force #-}

  goUH :: UnfoldHead -> S.Tm
  goUH = \case
    UHMeta x   -> S.Meta x
    UHTopDef x -> S.TopDef x

  goFH :: FlexHead -> IO S.WTm
  goFH = \case
    FHMeta m'           -> if m == m' then throwIO CantUnify else pure (S.WMeta m')
    FHCoeRefl _ a b p t -> S.WCoe <$> go a <*> go b <*> go p <*> go t
    FHCoeMax _ a b p t  -> S.WCoe <$> go a <*> go b <*> go p <*> go t
    FHEqMax _ a t u     -> S.WEq <$> go a <*> go t <*> go u

  goRH :: RigidHead -> IO S.WTm
  goRH = \case
    RHLocalVar x        -> case IM.lookup (coerce x) (ren pren) of
                             Nothing -> throwIO CantUnify
                             Just x' -> pure (S.WLocalVar (lvlToIx (dom pren) x'))
    RHPostulate x       -> pure (S.WPostulate x)
    RHCoe a b p t       -> S.WCoe <$> go a <*> go b <*> go p <*> go t
    RHRefl a t          -> S.WRefl <$> go a <*> go t
    RHSym a t u p       -> S.WSym <$> go a <*> go t <*> go u <*> go p
    RHTrans a x y z p q -> S.WTrans <$> go a <*> go x <*> go y <*> go z <*> go p <*> go q
    RHAp a b f x y p    -> S.WAp <$> go a <*> go b <*> go f <*> go x <*> go y <*> go p
    RHExfalso u a p     -> S.WExfalso u <$> go a <*> go p

  in case force v of
    Rigid h sp     -> do {h <- goRH h; wrenameSp m CSFlex pren (S h) sp}
    Flex h sp      -> do {h <- goFH h; wrenameSp m CSFlex pren (S h) sp}
    Unfold h sp t  -> case st of
                        CSRigid -> wrenameSp m CSFlex pren (goUH h) sp
                                   `catch` \_ -> wrename m CSFull pren (S t)
                        CSFlex  -> throwIO CantUnify
                        _       -> impossible
    Eq a t u v     -> unS <$> go v
    Pair t tu u uu -> S.WPair <$> go t <*> pure tu <*> go u <*> pure uu
    Lam x i a au t -> S.WLam x i <$> go a <*> pure au <*> goBind t
    Sg x a au b bu -> S.WSg x <$> go a <*> pure au <*> goBind b <*> pure bu
    Pi x i a au b  -> S.WPi x i <$> go a <*> pure au <*> goBind b
    U u            -> pure (S.WU u)
    Top            -> pure S.WTop
    Tt             -> pure S.WTt
    Bot            -> pure S.WBot


-- | Wrap a term in Lvl number of lambdas, getting the domain types
--   from a Ty.
lams :: Lvl -> Ty -> S.Tm -> S.Tm
lams l a t = go l 0 a t where
  go l l' a t | l == l' = t
  go l l' a t = case forceFUE l' a of
    Pi x i a au b ->
      S.Lam x i (quote l' DontUnfold a) au $ go l (l' + 1) (b $$ Var l') t
    _ -> impossible

solveMeta :: Lvl -> ConvState -> MetaVar -> Spine -> Val -> IO ()
solveMeta l st m sp rhs = do
  (S -> ma, S -> mu) <- readMeta m >>= \case
    MESolved{}     -> impossible
    MEUnsolved a u -> pure (unS a, unS u)

  case (st, unS (forceU mu)) of
    (CSFlex, S.WProp) -> pure ()
    (CSFlex, _      ) -> throwIO CantUnify
    _                 -> pure ()

  pren <- invert l sp
  rhs  <- rename m CSRigid pren rhs
  let sol = eval Nil 0 (lams (dom pren) ma rhs)
  D.write metaCxt (coerce m) (MESolved sol ma mu)



-- Unification
--------------------------------------------------------------------------------

unifySp :: Lvl -> ConvState -> Spine -> Spine -> IO ()
unifySp l st sp sp' = let
  go   = unify l st;   {-# inline go #-}
  goSp = unifySp l st; {-# inline goSp #-}

  goWithU :: S.U -> Val -> Val -> IO ()
  goWithU u t t' = case forceU u of
    S.Prop -> unify l CSFlex t t' `catch` \_ -> pure ()
    _      -> go t t'
  {-# inline goWithU #-}

  goProjField :: Spine -> Spine -> Int -> IO ()
  goProjField sp          sp' 0 = goSp sp sp'
  goProjField (SProj2 sp) sp' n = goProjField sp sp' (n - 1)
  goProjField _           _   _ = throwIO CantUnify

  in case Spine2 sp sp' of
    Spine2 (SNil             ) (SNil                ) -> pure ()
    Spine2 (SApp sp t u i    ) (SApp sp' t' u' i'   ) -> goSp sp sp' >> goWithU u t t'
    Spine2 (SProj1 sp        ) (SProj1 sp'          ) -> goSp sp sp'
    Spine2 (SProj2 sp        ) (SProj2 sp'          ) -> goSp sp sp'
    Spine2 (SProjField sp x n) (SProjField sp' x' n') -> goSp sp sp' >> unless (n == n) (throwIO CantUnify)
    Spine2 (SProjField sp x n) (SProj1 sp'          ) -> goProjField sp' sp n
    Spine2 (SProj1 sp        ) (SProjField sp' x' n') -> goProjField sp sp' n'
    Spine2 (SCoeSrc a b p t  ) (SCoeSrc a' b' p' t' ) -> goSp a a' >> go b b' >> go t t'
    Spine2 (SCoeTgt a b p t  ) (SCoeTgt a' b' p' t' ) -> go a a' >> goSp b b' >> go t t'
    Spine2 (SCoeComp a b p t ) (SCoeComp a' b' p' t') -> go a a' >> go b b' >> goSp t t'
    Spine2 (SEqType a t u    ) (SEqType a' t' u'    ) -> goSp a a' >> go t t' >> go u u'
    Spine2 (SEqSetLhs t u    ) (SEqSetLhs t' u'     ) -> goSp t t' >> go u u'
    Spine2 (SEqSetRhs t u    ) (SEqSetRhs t' u'     ) -> go t t' >> goSp u u'
    _                                                 -> throwIO CantUnify

unifyU :: ConvState -> S.U -> S.U -> IO ()
unifyU st u u' = case S.U2 (forceU u) (forceU u') of
  S.U2 (S.Set   ) (S.Set    )             -> pure ()
  S.U2 (S.Max xs) (S.Max xs') | xs == xs' -> pure ()
  S.U2 (S.Max xs) (S.Prop   )             -> S.forUMax xs \x -> solveU st x S.Prop
  S.U2 (S.Prop  ) (S.Max xs )             -> S.forUMax xs \x -> solveU st x S.Prop
  S.U2 (S.UVar x) (u        )             -> solveU st x u
  S.U2 (u       ) (S.UVar x )             -> solveU st x u
  S.U2 (u       ) (u'       )             -> throwIO CantUnify

unify :: Lvl -> ConvState -> Val -> Val -> IO ()
unify l st t t' = let
  go   = unify l st;   {-# inline go #-}
  goSp = unifySp l st; {-# inline goSp #-}

  force :: Val -> Val
  force t = case st of
    CSFull  -> forceFU l t
    _       -> forceF  l t
  {-# inline force #-}

  goWithU :: S.U -> Val -> Val -> IO ()
  goWithU u t t' = case forceU u of
    S.Prop -> unify l CSFlex t t' `catch` \_ -> pure ()
    _      -> go t t'
  {-# inline goWithU #-}

  goUH :: UnfoldHead -> UnfoldHead -> IO ()
  goUH h h' = case (h, h') of
    (UHMeta x  , UHMeta x'  ) | x == x' -> pure ()
    (UHTopDef x, UHTopDef x') | x == x' -> pure ()
    _                                   -> throwIO CantUnify
  {-# inline goUH #-}

  goLvl :: Lvl -> Lvl -> IO ()
  goLvl x x' = unless (x == x') (throwIO CantUnify)
  {-# inline goLvl #-}

  goMeta :: MetaVar -> MetaVar -> IO ()
  goMeta x x' = unless (x == x') (throwIO CantUnify)
  {-# inline goMeta #-}

  goMax :: S.UMax -> S.UMax -> IO ()
  goMax xs xs' = unifyU st (S.Max xs) (S.Max xs')
  {-# inline goMax #-}

  goRH :: RigidHead -> RigidHead -> IO ()
  goRH h h' = case (h, h') of
    (RHLocalVar x       , RHLocalVar x'            ) -> goLvl x x'
    (RHPostulate x      , RHPostulate x'           ) -> goLvl x x'
    (RHRefl a t         , RHRefl a' t'             ) -> go a a' >> go t t'
    (RHSym a t u p      , RHSym a' t' u' p'        ) -> go a a' >> go t t' >> go u u' >> go p p'
    (RHAp a b f x y p   , RHAp a' b' f' x' y' p'   ) -> go a a' >> go b b' >> go f f' >>
                                                        go x x' >> go y y' >> go p p'
    (RHTrans a x y z p q, RHTrans a' x' y' z' p' q') -> go a a' >> go x x' >> go y y' >>
                                                        go z z' >> go p p' >> go q q'
    (RHExfalso u a t    , RHExfalso u' a' t'       ) -> unifyU st u u' >> go a a'
    (RHCoe a b p t      , RHCoe a' b' p' t'        ) -> go a a' >> go b b' >> go t t'
    _                                                -> throwIO CantUnify

  goFH :: FlexHead -> FlexHead -> IO ()
  goFH h h' = case (h, h') of
    (FHMeta x            , FHMeta x'                ) -> goMeta x x'
    (FHMeta x            , _                        ) -> throwIO CantUnify
    (FHCoeRefl x a b p t , FHCoeRefl x' a' b' p' t' ) -> goMeta x x' >> go a a' >> go b b' >> go t t'
    (FHCoeRefl x _ _ _ _ , _                        ) -> throwIO CantUnify
    (FHCoeMax xs a b p t , FHCoeMax xs' a' b' p' t' ) -> goMax xs xs' >> go a a' >> go b b' >> go t t'
    (FHCoeMax xs _ _ _ _ , _                        ) -> throwIO CantUnify
    (FHEqMax xs a t u    , FHEqMax xs' a' t' u'     ) -> goMax xs xs' >> go a a' >> go t t' >> go u u'
    (FHEqMax xs a t u    , _                        ) -> throwIO CantUnify

  -- Here we try to match an Eq unfolding to a flexible Eq value. Note: postponing
  -- could also work here! It would be more precise, actually.
  eqUnfold :: Val -> Val -> Val -> Val -> Val -> IO ()
  eqUnfold a t u v t' = case t' of
    Flex (FHEqMax xs a' t' u') SNil -> go a a' >> go t t' >> go u u'
    Flex h' (SEqType a' t' u')      -> go a (Flex h' a') >> go t t' >> go u u'
    Flex h' (SEqSetLhs a' b')       -> go t (Flex h' a') >> go u b'
    Flex h' (SEqSetRhs a' b')       -> go t a' >> go u (Flex h' b')
    t'                              -> go v t'

  in case Val2 (force t) (force t') of

    -- unfolding
    Val2 (Unfold h sp t) (Unfold h' sp' t') -> case st of
      CSRigid -> (goUH h h' >> goSp sp sp') `catch` \_ -> unify l CSFull (S t) (S t')
      CSFlex  -> throwIO CantUnify
      _       -> impossible
    Val2 (Unfold h sp t) t' -> case st of
      CSRigid -> go (S t) t'
      CSFlex  -> throwIO CantUnify
      _       -> impossible
    Val2 t (Unfold h' sp' t') -> case st of
      CSRigid -> go t (S t')
      CSFlex  -> throwIO CantUnify
      _       -> impossible

    -- canonical
    Val2 (Pi _ i a au b ) (Pi _ i' a' au' b' ) -> unifyU st au au' >> go a a' >>
                                                  unify (l + 1) st (b $$ Var l) (b' $$ Var l)
    Val2 (Sg _ a au b bu) (Sg _ a' au' b' bu') -> unifyU st au au' >> unifyU st bu bu' >> go a a' >>
                                                  unify (l + 1) st (b $$ Var l) (b' $$ Var l)
    Val2 (U u           ) (U u'              ) -> unifyU st u u'
    Val2 (Top           ) (Top               ) -> pure ()
    Val2 (Tt            ) (Tt                ) -> pure ()
    Val2 (Bot           ) (Bot               ) -> pure ()

    -- rigid
    Val2 (Rigid h sp    ) (Rigid h' sp'      ) -> goRH h h' >> goSp sp sp'

    -- eta
    Val2 (Lam _ _ _ _ t ) (Lam _ _ _ _ t'    ) -> unify (l + 1) st (t $$ Var l) (t' $$ Var l)
    Val2 (Lam _ i _ u t ) (t'                ) -> unify (l + 1) st (t $$ Var l) (vApp t' (Var l) u i)
    Val2 (t             ) (Lam _ i' _ u' t'  ) -> unify (l + 1) st (vApp t (Var l) u' i') (t' $$ Var l)

    Val2 (Pair t tu u uu) (Pair t' tu' u' uu') -> goWithU tu t t' >> goWithU uu u u'
    Val2 (Pair t tu u uu) (t'                ) -> goWithU tu t (vProj1 t') >> goWithU uu u (vProj2 t')
    Val2 (t             ) (Pair t' tu' u' uu') -> goWithU tu' (vProj1 t) t' >> goWithU uu' (vProj2 t) u'

    -- Eq unfold (TODO: when to postpone instead?)
    Val2 (Eq _ _ _ v) (Eq _ _ _ v')    -> go v v'
    Val2 (Eq a t u v) t'               -> eqUnfold a t u v t'
    Val2 t            (Eq a' t' u' v') -> eqUnfold a' t' u' v' t

    -- Note: we don't peel off flex Eq and Coe from equation sides!  This makes
    -- unification rather weak now. The proper solution is to postpone them.
    -- The approximate solution is to equate any flex/rigid Eq/Coe with any
    -- flex/rigid Eq/Coe. This would require a nasty amount of pattern
    -- matching. We'll see how the current version works out.

    -- Flex
    Val2 (Flex (FHMeta x) sp) (Flex (FHMeta x') sp') | x == x' -> goSp sp sp' -- TODO: intersect
    Val2 (Flex (FHMeta x) sp) t'                               -> solveMeta l st x sp t'
    Val2 t                    (Flex (FHMeta x') sp')           -> solveMeta l st x' sp' t
    Val2 (Flex h sp)          (Flex h' sp')                    -> goFH h h' >> goSp sp sp'

    _ -> throwIO CantUnify


--------------------------------------------------------------------------------

unifyTest l st t t' = unify l st (S t) (S t')
inspectS 'unifyTest
