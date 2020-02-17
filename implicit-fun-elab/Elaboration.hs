
-- TODO: - Only use elabcxt and unifycxt
--       - try to decorate errors with info when info is available (catch/rethrow)
--       - implement simple elab without telescope/pruning
--       - add pruning
--       - add telescopes

-- ISSUE : don't have any nonlinear solutions!

module Elaboration where

import Control.Exception
import Control.Monad
import Data.Foldable
import Data.IORef
import Data.Maybe
import Lens.Micro.Platform
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Types
import Evaluation
import ElabState

import Debug.Trace


-- Telescope constancy
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


-- newConstancy :: MId -> Spine -> Closure -> IO ()
-- newConstancy telMeta sp cl = do
--   x <- fresh <$> view vals <*> pure "_"
--   ~codomain <- applyM cl (VVar x)
--   constM <- newMetaEntry (Constancy telMeta sp x codomain mempty)
--   tryConstancy constM

-- | Attempt to solve a constancy constraint.
tryConstancy :: MId -> IO ()
tryConstancy constM = lookupMeta constM >>= \case
  Constancy cxt telMeta sp codomain blockers -> do

    -- clear blockers
    forM_ (IS.toList blockers) $ \m -> do
      modifyMeta m $ \case
        Unsolved ms a -> Unsolved (IS.delete constM ms) a
        Solved t      -> Solved t
        Constancy{}   -> error "impossible"

    writeMeta constM $ Constancy cxt telMeta sp codomain mempty

    lookupMeta telMeta >>= \case
      Constancy{} -> error "impossible"
      Solved{}    -> pure ()
      Unsolved{}  ->
        case occurs (cxt^.len + 1) (cxt^.len) codomain of
          None    -> solveMeta cxt telMeta sp VTEmpty   -- no dependency, tel is empty
          Rigid   -> pure ()                            -- certain dependency
          Flex ms -> do   -- update blockers

            -- set new blockers
            forM_ (IS.toList ms) $ \m ->
              modifyMeta m $ \case
                Unsolved ms a -> Unsolved (IS.insert constM ms) a
                _             -> error "impossible"

            writeMeta constM $ Constancy cxt telMeta sp codomain ms

  _ -> error "impossible"


newConstancy :: UnifyCxt -> MId -> Spine -> (Val -> Val) -> IO ()
newConstancy cxt telMeta sp b = do
  let ~codomain = b (VVar (cxt^.len))
  undefined

-- newConstancy :: MId -> Spine -> Closure -> UnifyM ()
-- newConstancy telMeta sp cl = do
--   x <- fresh <$> view vals <*> pure "_"
--   ~codomain <- applyM cl (VVar x)
--   constM <- newMetaEntry (Constancy telMeta sp x codomain mempty)
--   tryConstancy constM


-- Unification
--------------------------------------------------------------------------------

-- | Checks that a spine consists only of distinct bound vars.
--   Returns a partial variable renaming on success, alongside the size
--   of the spine.
checkSp :: Spine -> IO (Renaming, Lvl)
checkSp = go . forceSp where
  go :: Spine -> IO (Renaming, Lvl)
  go = \case
    SNil        -> pure (mempty, 0)
    SApp sp u i -> do
      (!r, !d) <- go sp
      case force u of
        VVar x | IM.member x r -> throwIO $ NonLinearSpine x
               | otherwise     -> pure (IM.insert x d r, d + 1)
        _      -> throwIO SpineNonVar
    SAppTel a sp u -> do
      (!r, !d) <- go sp
      case force u of
        VVar x | IM.member x r -> throwIO $ NonLinearSpine x
               | otherwise     -> pure (IM.insert x d r, d + 1)
        _    -> throwIO SpineNonVar
    SProj1 _ -> throwIO SpineProjection
    SProj2 _ -> throwIO SpineProjection

-- | Close a type in a cxt by wrapping it in Pi types and explicit weakenings.
closingTy :: UnifyCxt -> Ty -> Ty
closingTy (UCxt TNil           []     d) b = b
closingTy (UCxt (TDef tys a)   (x:ns) d) b = closingTy (UCxt tys ns (d-1)) (Skip b)
closingTy (UCxt (TBound tys a) (x:ns) d) b = closingTy (UCxt tys ns (d-1)) (Pi x Expl (quote (d-1) a) b)
closingTy _                              _ = error "impossible"

-- | Close a term by wrapping it in `Int` number of lambdas, while taking the domain
--   types from the `VTy`.
closingTm :: (VTy, Int) -> Tm -> Tm
closingTm = go 0 where
  go d (a, 0)   rhs = rhs
  go d (a, len) rhs = case force a of
    VPi x i a b  -> Lam x i (quote d a)  $ go (d + 1) (b (VVar d), len-1) rhs
    VPiTel x a b -> LamTel x (quote d a) $ go (d + 1) (b (VVar d), len-1) rhs
    _            -> error "impossible"

-- | Strengthen a value, returns quoted normal result. This performs scope
--   checking, occurs checking and (recursive) pruning at the same time.
strengthen :: Str -> Val -> IO Tm
strengthen str = go where

  -- we only prune all-variable spines with illegal var occurrences,
  -- we don't prune illegal cyclic meta occurrences.
  prune :: MId -> Spine -> IO ()
  prune m sp = do

    let pruning :: Maybe [Bool]
        pruning = go [] sp where
          go acc SNil                    = pure acc
          go acc (SApp sp (VVar x) i)    = go (isJust (IM.lookup x (str^.ren)) : acc) sp
          go acc (SAppTel _ sp (VVar x)) = go (isJust (IM.lookup x (str^.ren)) : acc) sp
          go _   _                       = Nothing

    case pruning of
      Nothing                    -> pure ()  -- spine is not a var substitution
      Just pruning | and pruning -> pure ()  -- no pruneable vars
      Just pruning               -> do

        metaTy <- lookupMeta m >>= \case
          Unsolved _ a -> pure a
          _            -> error "impossible"

        -- note: this can cause recursive pruning of metas in types
        (prunedTy :: Ty) <- do
          let go :: [Bool] -> Str -> VTy -> IO Ty
              go [] str a = strengthen str a
              go (True:pr) str (force -> VPi x i a b) =
                Pi x i <$> strengthen str a <*> go pr (liftStr str) (b (VVar (str^.cod)))
              go (True:pr) str (force -> VPiTel x a b) =
                PiTel x <$> strengthen str a <*> go pr (liftStr str) (b (VVar (str^.cod)))
              go (False:pr) str (force -> VPi x i a b) =
                go pr (skipStr str) (b (VVar (str^.cod)))
              go (False:pr) str (force -> VPiTel x a b) =
                go pr (skipStr str) (b (VVar (str^.cod)))
              go _ _ _ = error "impossible"

          go pruning (Str 0 0 mempty Nothing) metaTy

        m' <- newMetaEntry $ Unsolved mempty (eval VNil prunedTy)

        let argNum = length pruning
            body = go pruning metaTy (Meta m') 0 where
              go [] a acc d = acc
              go (True:pr) (force -> VPi x i a b) acc d =
                go pr (b (VVar d)) (App acc (Var (argNum - d - 1)) i) (d + 1)
              go (True:pr) (force -> VPiTel x a b) acc d =
                go pr (b (VVar d)) (AppTel (quote argNum a) acc (Var (argNum - d - 1))) (d + 1)
              go (False:pr) (force -> VPi x i a b) acc d =
                go pr (b (VVar d)) acc (d + 1)
              go (False:pr) (force -> VPiTel x a b) acc d =
                go pr (b (VVar d)) acc (d + 1)
              go _ _ _ _ = error "impossible"

        let rhs = closingTm (metaTy, argNum) body
        -- traceShowM ("pruned", pruning, quote 0 metaTy, prunedTy, rhs)
        writeMeta m $ Solved (eval VNil rhs)

  go t = case force t of
    VNe (HVar x) sp  -> case IM.lookup x (str^.ren) of
                          Nothing -> throwIO $ ScopeError x
                          Just x' -> goSp (Var (str^.dom - x' - 1)) (forceSp sp)
    VNe (HMeta m) sp -> if Just m == str^.occ then
                          throwIO OccursCheck
                        else do
                          prune m sp
                          case force (VNe (HMeta m) sp) of
                            VNe (HMeta m) sp -> goSp (Meta m) sp
                            _                -> error "impossible"

    VPi x i a b      -> Pi x i <$> go a <*> goBind b
    VLam x i a t     -> Lam x i <$> go a <*> goBind t
    VU               -> pure U
    VTel             -> pure Tel
    VRec a           -> Rec <$> go a
    VTEmpty          -> pure TEmpty
    VTCons x a b     -> TCons x <$> go a <*> goBind b
    VTempty          -> pure Tempty
    VTcons t u       -> Tcons <$> go t <*> go u
    VPiTel x a b     -> PiTel x <$> go a <*> goBind b
    VLamTel x a t    -> LamTel x <$> go a <*> goBind t

  goBind t = strengthen (liftStr str) (t (VVar (str^.cod)))

  goSp h = \case
    SNil           -> pure h
    SApp sp u i    -> App <$> goSp h sp <*> go u <*> pure i
    SAppTel a sp u -> AppTel <$> go a <*> goSp h sp <*> go u
    SProj1 sp      -> Proj1 <$> goSp h sp
    SProj2 sp      -> Proj2 <$> goSp h sp

solveMeta :: UnifyCxt -> MId -> Spine -> Val -> IO ()
solveMeta cxt m sp rhs = do

  -- these normal forms are only used in error reporting
  let ~topLhs = quote (cxt^.len) (VNe (HMeta m) sp)
      ~topRhs = quote (cxt^.len) rhs

  (ren, spLen) <- checkSp sp
         `catch` (throwIO . SpineError (cxt^.names) topLhs topRhs)

  rhs <- strengthen (Str spLen (cxt^.len) ren (Just m)) rhs
         `catch` (throwIO . StrengtheningError (cxt^.names) topLhs topRhs)

  (blocked, metaTy) <- lookupMeta m >>= \case
    Unsolved blocked a -> pure (blocked, a)
    _                  -> error "impossible"

  let closedRhs = closingTm (metaTy, spLen) rhs
  writeMeta m (Solved (eval VNil closedRhs))

  -- try solving unblocked constraints
  forM_ (IS.toList blocked) tryConstancy


freshMeta :: UnifyCxt -> VTy -> IO Tm
freshMeta cxt (quote (cxt^.len) -> a) = do
  let metaTy = closingTy cxt a
  m <- newMetaEntry $ Unsolved mempty (eval VNil metaTy)

  -- apply meta to bound vars
  let appVars TNil                           = (Meta m, 0)
      appVars (TDef   (appVars -> (t, d)) _) = (t, d + 1)
      appVars (TBound (appVars -> (t, d)) _) = (App t (Var (cxt^.len - d - 1)) Expl, d + 1)

  pure $ fst $ appVars (cxt^.types)

unify :: Cxt -> Val -> Val -> IO ()
unify cxt l r =
  unify' (cxt^.ucxt) l r
  `catch`
  (report (cxt^.names) . UnifyErrorWhile (quote (cxt^.len) l) (quote (cxt^.len) r))

  where
  unify' cxt l r = go l r where

    unifyError =
      throwIO $ UnifyError (cxt^.names) (quote (cxt^.len) l) (quote (cxt^.len) r)

    go t t' = case (force t, force t') of
      (VLam x _ a t, VLam _ _ _ t')            -> goBind x a t t'
      (VLam x i a t, t')                       -> goBind x a t (\v -> vApp t' v i)
      (t, VLam x' i' a' t')                    -> goBind x' a' (\v -> vApp t v i') t'
      (VPi x i a b, VPi x' i' a' b') | i == i' -> go a a' >> goBind x a b b'
      (VU, VU)                                 -> pure ()
      (VTel, VTel)                             -> pure ()
      (VRec a, VRec a')                        -> go a a'
      (VTEmpty, VTEmpty)                       -> pure ()
      (VTCons x a b, VTCons x' a' b')          -> go a a' >> goBind x a b b'
      (VTempty, VTempty)                       -> pure ()
      (VTcons t u, VTcons t' u')               -> go t t' >> go u u'
      (VPiTel x a b, VPiTel x' a' b')          -> go a a' >> goBind x a b b'
      (VLamTel x a t, VLamTel x' a' t')        -> goBind x a t t'
      (VNe h sp, VNe h' sp') | h == h'         -> goSp (forceSp sp) (forceSp sp')
      (VNe (HMeta m) sp, t')                   -> solveMeta cxt m sp t'
      (t, VNe (HMeta m') sp')                  -> solveMeta cxt m' sp' t
      _                                        -> unifyError

    goBind x a t t' =
      let UCxt tys ns d = cxt
      in unify' (UCxt (TBound tys a) (x:ns) (d + 1)) (t (VVar d)) (t' (VVar d))

    -- TODO: forcing spine while unifying
    goSp sp sp' = case (sp, sp') of
      (SNil, SNil)                            -> pure ()
      (SApp sp u i, SApp sp' u' i') | i == i' -> goSp sp sp' >> go u u'
      (SAppTel _ sp u, SAppTel _ sp' u')      -> goSp sp sp' >> go u u'
      _                                       -> error "impossible"


-- Elaboration
--------------------------------------------------------------------------------

emptyCxt :: Cxt
emptyCxt = Cxt VNil TNil [] [] 0

emptyUCxt :: UnifyCxt
emptyUCxt = UCxt TNil [] 0

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
    Nothing -> throwIO (e & pos .~ Just p)
    _       -> throwIO e

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
          unify cxt (eval (cxt^.vals) ann) a
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
      unify cxt va topA
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
        VNe (HMeta m) sp -> do
          a    <- eval (cxt^.vals) <$> freshMeta (cxt^.ucxt) VU
          cod  <- freshMeta (bind "x" NOInserted a cxt^.ucxt) VU
          let b ~x = eval (VDef (cxt^.vals) x) cod
          unify cxt (VNe (HMeta m) sp) (VPi "x" Expl a b)
          u <- check cxt u a
          pure (App t u i, b (eval (cxt^.vals) u))
        _ ->
          report (cxt^.names) $ ExpectedFunction (quote (cxt^.len) va)

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
