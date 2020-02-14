
-- TODO: - Only use elabcxt and unifycxt
--       - try to decorate errors with info when info is available (catch/rethrow)
--       - implement simple elab without telescope/pruning
--       - add pruning
--       - add telescopes

-- ISSUE : don't have any nonlinear solutions!

module Elaboration where

import Data.Foldable
import Control.Exception
import Control.Monad
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import Data.IORef
import Lens.Micro.Platform

import Types
import Evaluation
import ElabState

import Debug.Trace

-- occurrence check for constancy
--------------------------------------------------------------------------------

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

-- pruning
--------------------------------------------------------------------------------

-- | A partial mapping from levels to levels. Undefined domain reresents
--   out-of-scope or "illegal" variables.
type Renaming = IM.IntMap Lvl

-- unification
--------------------------------------------------------------------------------

-- | Returns a partial renaming and the length of the spine.
--   Nonlinear spine is always an error. Throws SpineError.
checkSp :: Spine -> (Renaming, Lvl)
checkSp = go . forceSp where
  go :: Spine -> (Renaming, Lvl)
  go = \case
    SNil        -> (mempty, 0)
    SApp sp u i -> case go sp of
      (!r, !d) -> case force u of
        VVar x | IM.member x r -> throw $ NonLinearSpine x
               | otherwise     -> (IM.insert x d r, d + 1)
        _      -> throw SpineNonVar
    SAppTel a sp u -> case go sp of
      (!r, !d) -> case force u of
        VVar x | IM.member x r -> throw $ NonLinearSpine x
               | otherwise     -> (IM.insert x d r, d + 1)
        _    -> throw SpineNonVar
    SProj1 _ -> throw SpineProjection
    SProj2 _ -> throw SpineProjection


data Str = Str {
  _strDom :: Lvl,           -- ^ size of renaming domain
  _strCod :: Lvl,           -- ^ size of renaming codomain
  _strRen :: IM.IntMap Lvl, -- ^ partial renaming
  _strOcc :: Maybe MId      -- ^ meta for occurs strengthening
  }

makeFields ''Str

strengthen :: Str -> Val -> Tm
strengthen (Str d c r occurs) = go where

  prune m sp = Nothing

  go t = case force t of
    VNe (HVar x) sp  -> case IM.lookup x r of
                          Nothing -> throw $ ScopeError x
                          Just x' -> goSp (Var (d - x' - 1)) (forceSp sp)
    VNe (HMeta m) sp -> if Just m == occurs then
                          throw OccursCheck
                        else case prune m sp of
                          Nothing -> goSp (Meta m) (forceSp sp)
                          Just t  -> t
    VPi x i a b      -> Pi x i (go a) (goBind b)
    VLam x i a t     -> Lam x i (go a) (goBind t)
    VU               -> U
    VTel             -> Tel
    VRec a           -> Rec (go a)
    VTEmpty          -> TEmpty
    VTCons x a b     -> TCons x (go a) (goBind b)
    VTempty          -> Tempty
    VTcons t u       -> Tcons (go t) (go u)
    VPiTel x a b     -> PiTel x (go a) (goBind b)
    VLamTel x a t    -> LamTel x (go a) (goBind t)

  goBind t =
    strengthen (Str (d+1) (c+1) (IM.insert c d r) occurs) (t (VVar c))

  goSp h = \case
    SNil           -> h
    SApp sp u i    -> App (goSp h sp) (go u) i
    SAppTel a sp u -> AppTel (go a) (goSp h sp) (go u)
    SProj1 sp      -> Proj1 (goSp h sp)
    SProj2 sp      -> Proj2 (goSp h sp)


-- quoteRhs = undefined
-- quoteRhs :: UnifyCxt -> (Tm, Tm) -> MId -> (Renaming, Lvl) -> Val -> Tm
-- quoteRhs cxt (topLhs, topRhs) topMeta (r, splen) = rename (cxt^.len) splen r where

--   -- | Return a pruned and quoted meta-headed term
--   prune :: MId -> Spine -> Renaming -> Maybe Tm
--   prune m sp topRen = do

--     let getRenaming :: Spine -> Maybe (Lvl, Lvl, Renaming)
--         getRenaming = go where
--           go SNil = pure (0, 0, mempty)
--           go (SApp sp (VVar x) i) = do
--             (d, d', r) <- go sp
--             case IM.lookup x topRen of
--               Nothing -> pure (d+1, d', r)
--               Just{}  -> pure (d+1, d'+1, IM.insert d d' r)
--           go _ = Nothing

--     (d, d', r) <- getRenaming sp
--     guard $ d /= d'

--     let pruneTy :: VTy -> Tm
--         pruneTy = go 0 where
--           go i a | i == d = rename d d' r a
--           go i a = case force a of
--             VPi x i a b  -> _
--             VPiTel x a b -> _
--             _ -> error "impossible"

--     undefined

solveMeta :: UnifyCxt -> MId -> Spine -> Val -> IO ()
solveMeta cxt m sp rhs = do
  -- traceShowM ("solve", quote (cxt^.len) (VNe (HMeta m) sp), quote (cxt^.len) rhs)

  let ~lhst = quote (cxt^.len) (VNe (HMeta m) sp)
      ~rhst = quote (cxt^.len) rhs
  (r, d) <- pure $ checkSp sp
  rhs <- pure (strengthen (Str d (cxt^.len) r (Just m)) rhs)
         `catch` \e -> throw $ StrengtheningError (cxt^.names) lhst rhst e

  let mty = case lookupMeta m of
        Unsolved _ ty -> ty
        _             -> error "impossible"

  let lams :: (VTy, Lvl) -> Lvl -> Tm -> Tm
      lams (a, 0)     d rhs = rhs
      lams (a, splen) d rhs = case force a of
        VPi x i a b  -> Lam x i (quote d a) $ lams (b (VVar d), splen-1) (d + 1) rhs
        VPiTel x a b -> LamTel x (quote d a) $ lams (b (VVar d), splen-1) (d + 1) rhs
        _            -> error "impossible"

  rhs <- pure $ lams (mty, d) 0 rhs
  -- traceShowM ("solved", rhs)
  writeMetaIO m (Solved (eval VNil rhs))

freshMeta :: UnifyCxt -> VTy -> IO Tm
freshMeta cxt a = do
  a <- pure $ quote (cxt^.len) a
  m <- readIORef nextMId
  modifyIORef' nextMId (+1)

  let term TNil                        = (Meta m, 0)
      term (TDef   (term -> (t, d)) _) = (t, d + 1)
      term (TBound (term -> (t, d)) _) = (App t (Var (cxt^.len - d - 1)) Expl, d + 1)

  -- a bit inefficient because of dropping env definitions on each instantiation
  let ty TNil           []     vs = eval vs a
      ty (TDef   tys _) (x:ns) vs = ty tys ns vs
      ty (TBound tys b) (x:ns) vs = VPi x Expl b $ \ ~x -> ty tys ns (VDef vs x)
      ty _              _      _  = error "impossible"

  -- traceShowM ("freshmeta", fst $ term (cxt^.types))

  writeMetaIO m $ Unsolved mempty (ty (cxt^.types) (cxt^.names) VNil)
  pure $ fst $ term (cxt^.types)

unify :: UnifyCxt -> Val -> Val -> IO ()
unify cxt topT topT' = go topT topT' where

  ~unifyError =
    throw $ UnifyError (cxt^.names) (quote (cxt^.len) topT) (quote (cxt^.len) topT')

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
    (VNe h sp, VNe h' sp') | h == h'          -> goSp (forceSp sp) (forceSp sp')
    (VNe (HMeta m) sp, t')                    -> solveMeta cxt m sp t'
    (t, VNe (HMeta m') sp')                   -> solveMeta cxt m' sp' t
    _                                         -> unifyError

  goBind x a t t' =
    let UCxt tys ns d = cxt
    in unify (UCxt (TBound tys a) (x:ns) (d + 1)) (t (VVar d)) (t' (VVar d))

  goSp sp sp' = case (sp, sp') of
    (SNil, SNil)                            -> pure ()
    (SApp sp u i, SApp sp' u' i') | i == i' -> goSp sp sp' >> go u u'
    (SAppTel a sp u, SAppTel a' sp' u')     -> go a a' >> goSp sp sp' >> go u u'
    _                                       -> unifyError

-- Elaboration
--------------------------------------------------------------------------------

emptyCxt :: Cxt
emptyCxt = Cxt VNil TNil [] [] 0

bind :: Name ->  NameOrigin -> VTy -> Cxt -> Cxt
bind x o a (Cxt vs tys ns no d) =
  Cxt (VSkip vs) (TBound tys a) (x:ns) (o:no) (d + 1)

define :: Name -> VTy -> Val -> Cxt -> Cxt
define x a ~t (Cxt vs tys ns no d) =
  Cxt (VDef vs t) (TDef tys a) (x:ns) (NOSource:no) (d + 1)

insert :: Cxt -> MetaInsertion -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt False act = act
insert cxt True  act = do
  (t, va) <- act
  let go t va = case force va of
        VPi x Impl a b -> do
          m <- freshMeta (cxt^.ucxt) a
          let mv = eval (cxt^.vals) m
          go (App t m Impl) (b mv)
        va -> pure (t, va)
  go t va

addSrcPos :: SPos -> IO a -> IO a
addSrcPos p act = act `catch` \(e::Err) ->
  case e^.pos of
    Nothing -> throw (e & pos .~ Just p)
    _       -> throw e

check :: Cxt -> Raw -> VTy -> IO Tm
check cxt topT ~topA = do
  -- case topT of
  --   RSrcPos{} -> pure ()
  --   _ -> traceShowM ("check", topT, quote (cxt^.len) topA)

  res <- case (topT, force topA) of

    (RSrcPos p t, a) ->
      addSrcPos p (check cxt t a)

    (RLam x ann i t, VPi x' i' a b) | i == i' -> do
      -- let ~na = quote (cxt^.len) a
      -- traceShowM ("check lam domain", na)
      ann <- case ann of
        Just ann -> do
          ann <- check cxt ann VU
          unify (cxt^.ucxt) (eval (cxt^.vals) ann) a
          pure ann
        Nothing ->
          pure $ quote (cxt^.len) a
      t <- check (bind x NOSource a cxt) t (b (VVar (cxt^.len)))
      pure $ Lam x i ann t

    (t, VPi x Impl a b) -> do
      t <- check (bind x NOInserted a cxt) t (b (VVar (cxt^.len)))
      pure $ Lam x Impl (quote (cxt^.len) a) t

    (RLet x a t u, topA) -> do
      a <- check cxt a VU
      let ~va = eval (cxt^.vals) a
      t <- check cxt t va
      let ~vt = eval (cxt^.vals) t
      u <- check (define x va vt cxt) u topA
      pure $ Let x a t u

    (RHole, topA) -> do
      freshMeta (cxt^.ucxt) topA

    (t, topA) -> do
      (t, va) <- infer cxt True t
      -- traceShowM ("invert", quote (cxt^.len) va, quote (cxt^.len) topA)

      unify (cxt^.ucxt) va topA
        `catch`
        \case
          (e :: UnifyError) -> do
            let na    = quote (cxt^.len) va
                ntopA = quote (cxt^.len) topA
            report (cxt^.names) $ UnifyErrorWhile na ntopA e

      pure t

  pure res

infer :: Cxt -> MetaInsertion -> Raw -> IO (Tm, VTy)
infer cxt ins t = do
  res <- case t of
    RSrcPos p t ->
      addSrcPos p $ infer cxt ins t

    RU -> pure (U, VU)

    RVar x -> insert cxt ins $ do
      let go :: [Name] -> [NameOrigin] -> Types -> Int -> IO (Tm, VTy)
          go (y:xs) (NOSource:os) (TSnoc _  a) i | x == y = pure (Var i, a)
          go (_:xs) (_       :os) (TSnoc as _) i = go xs os as (i + 1)
          go []     []            TNil         _ = report (cxt^.names) (NameNotInScope x)
          go _ _ _ _ = error "impossible"
      go (cxt^.names) (cxt^.nameOrigin) (cxt^.types) 0

    RPi x i a b -> do
      a <- check cxt a VU
      let ~va = eval (cxt^.vals) a
      b <- check (bind x NOSource va cxt) b VU
      pure (Pi x i a b, VU)

    RApp t u i -> insert cxt ins $ do
      (t, va) <- infer cxt (i == Expl) t
      case force va of
        VPi x i' a b -> do
          unless (i == i') $
            report (cxt^.names) $ IcitMismatch i i'
          u <- check cxt u a
          pure (App t u i, b (eval (cxt^.vals) u))
        _ ->
          report (cxt^.names) $ ExpectedFunction t

    RLam x ann i t -> insert cxt ins $ do
      a <- case ann of
        Just ann -> check cxt ann VU
        Nothing  -> freshMeta (cxt^.ucxt) VU
      let ~va = eval (cxt^.vals) a
      (t, b) <- infer (bind x NOSource va cxt) True t
      let ~nb = quote (cxt^.len + 1) b
      pure (Lam x i a t, VPi x i va $ \ ~x -> eval (VDef (cxt^.vals) x) nb)

    RHole -> do
      a <- freshMeta (cxt^.ucxt) VU
      let ~va = eval (cxt^.vals) a
      t <- freshMeta (cxt^.ucxt) va
      pure (t, va)

    RLet x a t u -> do
      a <- check cxt a VU
      let ~va = eval (cxt^.vals) a
      -- traceShowM ("infer let type", a)
      -- traceShowM ("infer let type nf", quote (cxt^.len) va)
      t <- check cxt t va
      let ~vt = eval (cxt^.vals) t
      (u, b) <- infer (define x va vt cxt) ins u
      pure (Let x a t u, b)

  -- case t of
  --   RSrcPos{} -> pure ()
  --   _ -> traceShowM ("inferred", t, quote (cxt^.len) (snd res))

  pure res
