{-# options_ghc -Wno-type-defaults #-}

-- 1. implement constancy, pattern unify, but no pruning
-- 2. implement pruning
-- 3. see if we can merge stuff

module Elaboration where

import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import Data.IORef

import Types
import Evaluation
import ElabState

-- occurrence check for the purpose of constancy
------------------------------------------------------------

data Occurs = Rigid | Flex IS.IntSet | None deriving (Eq, Show)

instance Semigroup Occurs where
  Flex ms <> Flex ms' = Flex (ms <> ms')
  Rigid   <> _        = Rigid
  _       <> Rigid    = Rigid
  None    <> r        = r
  l       <> None     = l

occurrence :: IS.IntSet -> Occurs
occurrence ms | IS.null  ms = Rigid
              | otherwise   = Flex ms

instance Monoid Occurs where
  mempty = None

occurs :: Lvl -> Lvl -> Val -> Occurs
occurs d topX = occurs' d mempty where

  occurs' :: Lvl -> IS.IntSet -> Val -> Occurs
  occurs' d ms = go where

    goSp ms sp = case forceSp sp of
      SNil           -> mempty
      SApp sp u i    -> goSp ms sp <> go u
      SAppTel a sp u -> go a <> goSp ms sp <> go u
      SProj1 sp      -> goSp ms sp
      SProj2 sp      -> goSp ms sp

    goBind t =
      occurs' (d + 1) ms (t (VVar d))

    go v = case force v of
      VNe (HVar x) sp | x == topX -> occurrence ms <> goSp ms sp
      VNe (HVar x) sp             -> goSp ms sp
      VNe (HMeta m) sp            -> goSp (IS.insert m ms) sp
      VPi _ i a b   -> go a <> goBind b
      VLam _ i a t  -> go a <> goBind t
      VU            -> mempty
      VTel          -> mempty
      VRec a        -> go a
      VTEmpty       -> mempty
      VTCons _ a b  -> go a <> goBind b
      VTempty       -> mempty
      VTcons t u    -> go t <> go u
      VPiTel x a b  -> go a <> goBind b
      VLamTel x a t -> go a <> goBind t

------------------------------------------------------------

-- If (Just l)   : rename to l
--    Nothing    : nonlinear var (error)
--    not in map : out-of-scope (error)
type SpineRenaming = IM.IntMap (Maybe Lvl)

-- | Expects a forced spine. Returns a partial renaming and the length of the spine.
checkSp :: ([Name], Tm, Tm) -> Spine -> (SpineRenaming, Lvl)
checkSp (report -> report, lhs, rhs) = go where
  go :: Spine -> (SpineRenaming, Lvl)
  go = \case
    SNil        -> (mempty, 0)
    SApp sp u i -> case go sp of
      (!r, !d) -> case force u of
        VVar x -> (IM.insert x (if IM.member x r then Nothing else Just d) r, d + 1)
        _      -> report $ SpineNonVar lhs rhs
    SAppTel a sp u -> case go sp of
      (!r, !d) -> case force u of
        VVar x -> (IM.insert x (if IM.member x r then Nothing else Just d) r, d + 1)
        _    -> report $ SpineNonVar lhs rhs
    SProj1 _ -> report SpineProjection
    SProj2 _ -> report SpineProjection

quoteRhs :: ([Name], Tm, Tm) -> MId -> (SpineRenaming, Lvl) -> Val -> Tm
quoteRhs (topNs, topLhs, topRhs) topMeta = go where

  go :: (SpineRenaming, Lvl) -> Val -> Tm
  go (!r, !d) v = case (go (r, d),
                     \t -> go (IM.insert d (Just d) r, d + 1) (t (VVar d))) of
    (go, goBind) -> case force v of
      VNe h sp ->
        let h' = case h of
              HMeta m | m == topMeta -> report topNs $ OccursCheck topLhs topRhs
              HMeta m -> Meta m
              HVar x -> case IM.lookup x r of
                Nothing        -> report topNs $ ScopeError topLhs topRhs (lvlName topNs x)
                Just Nothing   -> report topNs $ NonLinearSolution topLhs topRhs (lvlName topNs x)
                Just (Just x') -> Var (d - x' - 1)

            goSp SNil             = h'
            goSp (SApp sp u i)    = App (goSp sp) (go u) i
            goSp (SAppTel a sp u) = AppTel (go a) (goSp sp) (go u)
            goSp (SProj1 sp)      = Proj1 (goSp sp)
            goSp (SProj2 sp)      = Proj2 (goSp sp)

         in goSp (forceSp sp)

      VPi x i a b   -> Pi x i (go a) (goBind b)
      VLam x i a t  -> Lam x i (go a) (goBind t)
      VU            -> U
      VTel          -> Tel
      VRec a        -> Rec (go a)
      VTEmpty       -> TEmpty
      VTCons x a b  -> TCons x (go a) (goBind b)
      VTempty       -> Tempty
      VTcons t u    -> Tcons (go t) (go u)
      VPiTel x a b  -> PiTel x (go a) (goBind b)
      VLamTel x a t -> LamTel x (go a) (goBind t)

solveMeta :: [Name] -> Lvl -> MId -> Spine -> Val -> IO ()
solveMeta ns d m sp rhs = do
  let ~lhst = quote d (VNe (HMeta m) sp)
      ~rhst = quote d rhs
  sp  <- pure $ checkSp (ns, lhst, rhst) (forceSp sp)
  rhs <- pure $ quoteRhs (ns, lhst, rhst) m sp rhs

  let mty = case lookupMeta m of
        Unsolved _ ty -> ty
        _             -> error "impossible"

  let lams :: (VTy, Lvl) -> Lvl -> Tm -> Tm
      lams (a, 0)     d rhs = rhs
      lams (a, splen) d rhs = case force a of
        VPi x i a b  -> Lam x i (quote d a) $ lams (b (VVar d), splen-1) (d + 1) rhs
        VPiTel x a b -> LamTel x (quote d a) $ lams (b (VVar d), splen-1) (d + 1) rhs
        _            -> error "impossible"

  rhs <- pure $ lams (mty, snd sp) 0 rhs
  writeMetaIO m (Solved (eval VNil rhs))

freshMeta :: [Name] -> Types -> VTy -> IO Tm
freshMeta ns tys a = do
  a <- pure $ quote (typesLen tys) a
  m <- readIORef nextMId
  modifyIORef' nextMId (+1)

  let term TNil                        = (Meta m, 0)
      term (TDef   (term -> (t, d)) _) = (t, d + 1)
      term (TBound (term -> (t, d)) _) = (App t (Var d) Expl, d + 1)

  -- bit inefficient because of dropping env definitions on each instantiation
  let ty TNil           []     vs = eval vs a
      ty (TDef   tys _) (x:ns) vs = ty tys ns vs
      ty (TBound tys b) (x:ns) vs = VPi x Expl b $ \ ~x -> ty tys ns (VDef vs x)
      ty _              _      _  = error "impossible"

  writeMetaIO m $ Unsolved mempty (ty tys ns VNil)
  pure $ fst $ term tys

unify :: [Name] -> Types -> Lvl -> Val -> Val -> IO ()
unify ns tys d topT topT' = go topT topT' where

  ~ntopT  = quote (typesLen tys) topT
  ~ntopT' = quote (typesLen tys) topT'

  go t t' = case (force t, force t') of
    (VLam x _ a t, VLam _ _ _ t')             -> goBind x a t t'
    (VLam x i a t, t')                        -> goBind x a t (\v -> vApp t' v i)
    (t, VLam x' i' a' t')                     -> goBind x' a' (\v -> vApp t v i') t'
    (VPi x i a b, VPi x' i' a' b') | i == i'  -> go a a' >> goBind x a b b'
    (VU, VU)                                  -> pure ()
    (VTel, VTel)                              -> pure ()
    (VRec a, VRec a')                         -> go a a'
    (VTEmpty, VTEmpty)                        -> pure ()
    (VTCons x a b, VTCons x' a' b')           -> go a a' >> goBind x a b b'
    (VTempty, VTempty)                        -> pure ()
    (VTcons t u, VTcons t' u')                -> go t t' >> go u u'
    (VPiTel x a b, VPiTel x' a' b')           -> go a a' >> goBind x a b b'
    (VLamTel x a t, VLamTel x' a' t')         -> goBind x a t t'
    (VNe h sp, VNe h' sp') | h == h'          -> goSp sp sp'
    (VNe (HMeta m) sp, t')                    -> solveMeta ns d m sp t'
    (t, VNe (HMeta m') sp')                   -> solveMeta ns d m' sp' t
    _                                         -> report ns $ UnifyError ntopT ntopT'

  goBind x a t t' =
    unify (x:ns) (TBound tys a) (d + 1) (t (VVar d)) (t' (VVar d))

  goSp sp sp' = case (forceSp sp, forceSp sp') of
    (SNil, SNil)                            -> pure ()
    (SApp sp u i, SApp sp' u' i') | i == i' -> goSp sp sp' >> go u u'
    (SAppTel a sp u, SAppTel a' sp' u')     -> go a a' >> goSp sp sp' >> go u u'
    _                                       -> report ns $ UnifyError ntopT ntopT'
