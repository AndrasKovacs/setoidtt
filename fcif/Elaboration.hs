
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Elaboration where

{-|

Current design:
- eval is purely syntax-directed
- unif if universe-directed, but not type-directed
- Prop is not a subtype of Set
- ⊤ and ⊥ are in Prop, Π and Σ are universe-polymorphic
- exfalso and coe are univ-polymorphic in target

- simple projection unification (just drop matching projections from lhs and rhs)


OLD notes

- Eval is not relevance-directed, unification is
- Unification only appeals to irrelevance when the sides are rigidly disjoint.
  We can't just skip over irrelevant equations because we want to solve metas.

- PLANZ:
    - in surface lang, generic record types, polymorphic over Set/Prop
      - empty record type always in Prop
    - telescope functions only internally
    - glued evaluation
    - eval does *not* mark irrelevance, but unification is irrelevance-directed
      - we don't get a big benefit from not eval-ing irrelevant things, as we
        already have local eval.
    - binders marked with type + univ
    - fun applications marked with univ of argument
    - record projections marked with univ of record (from which we project)

    - work out faster pruning with glued eval
    - work out postponing in general
    - work out utilizing computing coercion for postponing
      - this requires types in spines (which we have even without
        full typed unif! Since we are already passing type env in unification,
        so we can grab the types of neutral heads)
      - The only remaining advantage of full typed unif seems to be Top eta in Set!

-}

import Control.Exception
import Control.Monad
import Data.Maybe
import Lens.Micro.Platform
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS

import Types
import qualified Evaluation as Eval
import EvalCxt
import ElabState
import Errors
import Pretty

-- import Debug.Trace

-- Context operations
--------------------------------------------------------------------------------

emptyCxt :: Cxt
emptyCxt = Cxt VNil TNil [] [] 0

-- | Add a bound variable.
bind :: Name -> NameOrigin -> VTy -> U -> Cxt -> Cxt
bind x o ~a au (Cxt vs tys ns no d) =
  Cxt (VSkip vs) (TBound tys a au) (x:ns) (o:no) (d + 1)

-- | Add a bound variable which comes from surface syntax.
bindSrc :: Name -> VTy -> U -> Cxt -> Cxt
bindSrc x = bind x NOSource

-- | Define a new variable.
define :: Name -> VTy -> U -> Val -> Cxt -> Cxt
define x ~a ~un ~t (Cxt vs tys ns no d) =
  Cxt (VDef vs t) (TDef tys a un) (x:ns) (NOSource:no) (d + 1)

-- | Lift ("skolemize") a value in an extended context to a function in a
--   non-extended context.
liftVal :: Cxt -> Val -> (Val -> Val)
liftVal cxt t ~x =
  Eval.eval (VDef (cxt^.vals) x) (cxt^.len + 1) $ Eval.quote (cxt^.len+1) t

-- Unification
--------------------------------------------------------------------------------

-- | Checks that a spine consists only of distinct bound vars.
--   Returns a partial variable renaming on success, alongside the size
--   of the spine, and the list of variables in the spine.
--   May throw SpineError.
checkSp :: Cxt -> Spine -> IO (Renaming, Lvl, [Lvl])
checkSp cxt = (over _3 reverse <$>) . go where
  go :: Spine -> IO (Renaming, Lvl, [Lvl])
  go = \case
    SNil           -> pure (mempty, 0, [])
    SApp sp u un i -> do
      (!r, !d, !xs) <- go sp
      case force cxt u of
        VVar x | IM.member x r -> throwIO $ NonLinearSpine x
               | otherwise     -> pure (IM.insert x d r, d + 1, x:xs)
        _      -> throwIO SpineNonVar
    SProj1{} -> throwIO SpineProjection
    SProj2{} -> throwIO SpineProjection

-- | Close a type in a cxt by wrapping it in Pi types and explicit weakenings.
closingTy :: Cxt -> Ty -> Ty
closingTy cxt = go (cxt^.types) (cxt^.names) (cxt^.len) where
  go TNil                  []     d b = b
  go (TDef tys a au)       (x:ns) d b = go tys ns (d-1) (Skip b)
  go (TBound tys a au)     (x:ns) d b =
    go tys ns (d-1) (Pi x Expl (Eval.quote (d-1) a) au b)
  go _                     _      _ _ = error "impossible"

-- | Close a term by wrapping it in `Int` number of lambdas, while taking the domain
--   types from the `VTy`, and the binder names from a list. If we run out of provided
--   binder names, we pick the names from Pi domains.
closingTm :: (VTy, Int, [Name]) -> Tm -> Tm
closingTm = go 0 where
  getName []     x = x
  getName (x:xs) _ = x

  go d (a, 0, _)   rhs = rhs
  go d (a, len, xs) rhs = case Eval.force d a of
    VPi (getName xs -> x) i a au b  ->
      Lam x i (Eval.quote d a) au $
        go (d + 1) (b (VVar d), len-1, drop 1 xs) rhs
    _            -> error "impossible"

data Relevance = Relevant | Irrelevant
 deriving (Eq, Show)

-- | Strengthens a value, returns a quoted normal result. This performs scope
--   checking, meta occurs checking and (recursive) pruning at the same time.
--   May throw StrengtheningError.
strengthen :: Relevance -> Str -> Val -> IO Tm
strengthen rel str = go where

  -- we only prune all-variable spines with illegal var occurrences,
  -- we don't prune illegal cyclic meta occurrences.
  prune :: MId -> Spine -> IO ()
  prune m sp = do

    let pruning :: Maybe [Bool]
        pruning = go [] sp where
          go acc SNil                    = pure acc
          go acc (SApp sp (VVar x) _ i)  = go (isJust (IM.lookup x (str^.ren)) : acc) sp
          go _   _                       = Nothing

    case pruning of
      Nothing                    -> pure () -- spine is not a var substitution
      Just pruning | and pruning -> pure () -- no pruneable vars
      Just pruning               -> do
        (metaTy, metaU) <- lookupMeta m >>= \case
          Unsolved a au -> pure (a, au)
          _             -> error "impossible"

        case (rel, forceU metaU) of
          (Irrelevant, Set) -> throw (RelevantMetaInIrrelevantMode m)
          _                 -> pure ()

        -- note: this can cause recursive pruning of metas in types
        (prunedTy :: Ty) <- do
          let go :: [Bool] -> Str -> VTy -> IO Ty
              go [] str a = strengthen rel str a
              go (True:pr) str (Eval.force (str^.cod) -> VPi x i a au b) =
                Pi x i <$> strengthen rel str a <*> pure au <*>
                      go pr (liftStr str) (b (VVar (str^.cod)))
              go (False:pr) str (Eval.force (str^.cod) -> VPi x i a un b) =
                go pr (skipStr str) (b (VVar (str^.cod)))
              go _ _ _ = error "impossible"

          go pruning (Str 0 0 mempty Nothing) metaTy

        m' <- newMeta (eval emptyCxt prunedTy) metaU

        let argNum = length pruning
            body = go pruning metaTy (Meta m') 0 where
              go :: [Bool] -> VTy -> _ -> _
              go [] a acc d = acc
              go (True:pr) (Eval.force argNum -> VPi x i a au b) acc d =
                go pr (b (VVar d))
                      (App acc (Var (argNum - d - 1)) au i) (d + 1)
              go (False:pr) (Eval.force argNum -> VPi x i a au b) acc d =
                go pr (b (VVar d)) acc (d + 1)
              go _ _ _ _ = error "impossible"

        let rhs = closingTm (metaTy, argNum, []) body
        writeMeta m $ Solved (eval emptyCxt rhs)

  go t = case Eval.force (str^.cod) t of
    VNe (HVar x) sp         -> case IM.lookup x (str^.ren) of
                                 Nothing -> throwIO $ ScopeError x
                                 Just x' -> goSp (Var (str^.dom - x' - 1)) sp
    VNe (HMeta m) sp        -> if Just m == str^.occ then
                                 throwIO OccursCheck
                               else do
                                 prune m sp
                                 case Eval.force (str^.cod) (VNe (HMeta m) sp) of
                                   VNe (HMeta m) sp -> goSp (Meta m) sp
                                   _                -> error "impossible"
    VNe (HCoe u a b p t) sp -> do h <- tCoe u <$> go a <*> go b <*> go p <*> go t
                                  goSp h sp
    VNe (HAxiom ax) sp      -> goSp (axiomToTm ax) sp
    VPi x i a au b          -> Pi x i <$> go a <*> pure au <*> goBind b
    VLam x i a au t         -> Lam x i <$> go a <*> pure au <*> goBind t
    VU u                    -> pure (U u)
    VTop                    -> pure Top
    VTt                     -> pure Tt
    VBot                    -> pure Bot
    VEqGlue _ _ _ b         -> go b
    VEq a x y               -> tEq <$> go a <*> go x <*> go y
    VSg x a au b bu         -> Sg x <$> go a <*> pure au <*> goBind b <*> pure bu
    VPair t tu u uu         -> Pair <$> go t <*> pure tu <*> go u <*> pure uu

  goBind t = strengthen rel (liftStr str) (t (VVar (str^.cod)))

  goSp h = \case
    SNil           -> pure h
    SApp sp u uu i -> App <$> goSp h sp <*> go u <*> pure uu <*> pure i
    SProj1 sp spu  -> Proj1 <$> goSp h sp <*> pure spu
    SProj2 sp spu  -> Proj2 <$> goSp h sp <*> pure spu

-- | May throw UnifyError.
solveMeta :: Cxt -> Relevance -> MId -> Spine -> Val -> IO ()
solveMeta cxt rel m sp rhs = do

  -- these normal forms are only used in error reporting
  let ~topLhs = quote cxt (VNe (HMeta m) sp)
      ~topRhs = quote cxt rhs

  (ren, spLen, spVars) <- checkSp cxt sp
         `catch` (throwIO . SpineError (cxt^.names) topLhs topRhs)
  rhs <- strengthen rel (Str spLen (cxt^.len) ren (Just m)) rhs
         `catch` (throwIO . StrengtheningError (cxt^.names) topLhs topRhs)

  (metaTy, metaU) <- lookupMeta m >>= \case
    Unsolved a au -> pure (a, au)
    _             -> error "impossible"

  case (rel, forceU metaU) of
    (Irrelevant, Set) -> throw (RelevantMetaInIrrelevantMode m)
    _                 -> pure ()

  let spVarNames = map (lvlName (cxt^.names)) spVars
  let closedRhs = closingTm (metaTy, spLen, spVarNames) rhs
  writeMeta m (Solved (eval emptyCxt closedRhs))

-- | Fresh meta creation attempts to immediately eta-expand
--   Sg and Top.
freshMeta :: Cxt -> VTy -> U -> IO Tm
freshMeta cxt a au = case force cxt a of
  VTop            -> pure Tt
  VSg x a au b bu -> do
    p1 <- freshMeta cxt a au
    p2 <- freshMeta cxt (b (eval cxt p1)) bu
    pure (Pair p1 au p2 bu)
  (quote cxt -> a) -> do
    let metaTy = closingTy cxt a
    m <- newMeta (eval emptyCxt metaTy) au

    let vars :: Types -> (Spine, Lvl)
        vars TNil                              = (SNil, 0)
        vars (TDef (vars -> (sp, !d)) _ _)     = (sp, d + 1)
        vars (TBound (vars -> (sp, !d)) _ un)  = (SApp sp (VVar d) un Expl, d + 1)

    let sp = fst $ vars (cxt^.types)
    pure (quote cxt (VNe (HMeta m) sp))


unifyTypes :: Cxt -> Val -> Val -> IO ()
unifyTypes cxt l r =
  unify Relevant cxt Set l r
  `catch`
  (report cxt . UnifyErrorWhile (quote cxt l) (quote cxt r))

-- | May throw UnifyError.
unify :: Relevance -> Cxt -> U -> Val -> Val -> IO ()
unify rel cxt un l r = go un l r where

  solveU :: UId -> U -> IO ()
  solveU x u = case rel of
    Irrelevant -> throw (RelevantMetaInIrrelevantMode x)
    _          -> writeU x (Just u)

  goU :: U -> U -> IO ()
  goU u u' = case (forceU u, forceU u') of
    (Set, Set)                      -> pure ()
    (UMax xs, UMax xs') | xs == xs' -> pure ()
    (UMax xs, Prop) -> forM_ (IS.toList xs) \x -> solveU x Prop
    (Prop, UMax xs) -> forM_ (IS.toList xs) \x -> solveU x Prop
    (UMeta x, u)    -> solveU x u
    (u, UMeta x)    -> solveU x u
    (u, u')         -> err (VU u) (VU u')

  err :: Val -> Val -> IO ()
  err l r =
    throwIO $ UnifyError (cxt^.names) (quote cxt l) (quote cxt r)

  go :: U -> Val -> Val -> IO ()
  go un t t' = case (rel, forceU un) of
    (Relevant, Prop) -> do
      unify Irrelevant cxt un t t' `catch` \(e :: UnifyError) -> pure ()

    (rel, un) -> case (force cxt t, force cxt t') of

      -- TODO: rigidity check. Also requires keeping track of rigid coercion,
      -- i.e. we have to know which coe is blocked on a meta and which one is blocked
      -- on a neutral.
      (VEq a t u,       VEq a' t' u'       ) -> go Set a a' >>  go Set t t' >> go Set u u'
      (VEq a t u,       VEqGlue a' t' u' b') -> go Set a a' >> go Set t t' >> go Set u u'
      (VEqGlue a t u b, VEq a' t' u'       ) -> go Set a a' >> go Set t t' >> go Set u u'
      (VEqGlue _ _ _ b, t'                 ) -> go Set b t'
      (t              , VEqGlue _ _ _ b'   ) -> go Set t b'

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

        (HVar x, HVar x') | x == x' -> goSp (err t t') sp sp'
        (HAxiom ax, HAxiom ax') -> case (ax, ax') of

          (ARefl, ARefl)            -> goSp (err t t') sp sp'
          (ASym, ASym)              -> goSp (err t t') sp sp'
          (AAp , AAp )              -> goSp (err t t') sp sp'
          (AExfalso u, AExfalso u') -> goU u u' >> goSp (err t t') sp sp'
          _                         -> err t t'

        (HCoe u a b p t, HCoe u' a' b' p' t') -> do
          goU u u' >> go Set a a' >> go Set b b' >> go Prop p p' >> go u t t'

        (HMeta m, HMeta m') | m == m'   -> goSp (err t t') sp sp'
                            | otherwise -> try @SpineError (checkSp cxt sp) >>= \case
                                  Left{}  -> solveMeta cxt rel m' sp' (VNe (HMeta m) sp)
                                  Right{} -> solveMeta cxt rel m sp (VNe (HMeta m') sp')

        (HMeta m, h') -> solveMeta cxt rel m sp (VNe h' sp')
        (h, HMeta m') -> solveMeta cxt rel m' sp' (VNe h sp)
        _             -> err (VNe h sp) (VNe h' sp')

      (VNe (HMeta m) sp, t')  -> solveMeta cxt rel m sp t'
      (t, VNe (HMeta m') sp') -> solveMeta cxt rel m' sp' t
      (t, t')                 -> err t t'

  goBind :: Name -> VTy -> U -> U -> (Val -> Val) -> (Val -> Val) -> IO ()
  goBind x a au un t t' =
    let v = VVar (cxt^.len) in unify rel (bindSrc x a au cxt) un (t v) (t' v)

  goSp :: IO () -> Spine -> Spine -> IO ()
  goSp err sp sp' = case (sp, sp') of
    (SNil, SNil)                                   -> pure ()
    (SApp sp u uu i, SApp sp' u' uu' i') | i == i' -> goSp err sp sp' >>
                                                      goU uu uu' >> go uu u u'
    (SProj1 sp spu, SProj1 sp' spu')               -> goSp err sp sp' >> goU spu spu'
    (SProj2 sp spu, SProj2 sp' spu')               -> goSp err sp sp' >> goU spu spu'
    _                                              -> err



-- Elaboration
--------------------------------------------------------------------------------

newTy :: Cxt -> IO (Tm, U)
newTy cxt = do
  ua <- UMeta <$> newU
  a  <- freshMeta cxt (VU ua) Set
  pure (a, ua)

insert :: Cxt -> IO (Tm, VTy, U) -> IO (Tm, VTy, U)
insert cxt act = do
  (t, va, un) <- act
  let go :: Tm -> VTy -> IO (Tm, VTy)
      go t va = case force cxt va of
        VPi x Impl a au b -> do
          m <- freshMeta cxt a au
          let mv = eval cxt m
          go (App t m au Impl) (b mv)
        va -> pure (t, va)
  (a, va) <- go t va
  pure (a, va, un)

inferTy :: Cxt -> Raw -> IO (Tm, U)
inferTy cxt a = do
  (a, au, _) <- infer cxt a
  au <- case force cxt au of
    VU u -> pure u
    au@(VNe (HMeta{}) _) -> do
      u <- UMeta <$> newU
      unifyTypes cxt au (VU u)
      pure u
    au -> report cxt $ ExpectedType a (quote cxt au)
  pure (a, au)

-- | Check an equality proof.
checkEq :: Cxt -> Raw -> VTy -> Val -> Val -> IO Tm
checkEq cxt t a l r = case t of
  RSrcPos p t ->
    addSrcPos p (checkEq cxt t a l r)
  RRefl -> do
    unify Relevant cxt Set l r
    pure (tRefl (quote cxt a) (quote cxt l))
  RAppE (unSrc -> RSym) t -> do
    t <- checkEq cxt t a r l
    pure (tSym (quote cxt a) (quote cxt r) (quote cxt l) t)
  RAppE (unSrc -> RAppE (unSrc -> RTrans) p) q -> do
    mid <- freshMeta cxt a Set
    let ~vmid = eval cxt mid
    p <- checkEq cxt p a l vmid
    q <- checkEq cxt q a vmid r
    pure (tTrans (quote cxt a) (quote cxt l) mid (quote cxt r) p q)
  RAppE (unSrc -> RAppE (unSrc -> RAp) f) p -> do
    b <- freshMeta cxt VSet Set
    let ~vb = eval cxt b
    x <- freshMeta cxt vb Set
    let ~vx = eval cxt x
    y <- freshMeta cxt vb Set
    let ~vy = eval cxt y
    f <- check cxt f (VPi "_" Expl vb Set (const a)) Set
    let ~vf = eval cxt f
    unify Relevant cxt Set l (vApp vf (eval cxt x) Set Expl)
    unify Relevant cxt Set r (vApp vf (eval cxt y) Set Expl)
    p <- checkEq cxt p vb vx vy
    pure (tAp b (quote cxt a) f x y p)
  t ->
    check cxt t (vEq cxt a l r) Prop


check :: Cxt -> Raw -> VTy -> U -> IO Tm
check cxt topT (force cxt -> topA) ~topU = case (topT, unglue topA) of
  (RSrcPos p t, _) ->
    addSrcPos p (check cxt t topA topU)

  (RLam x ann i t, VPi x' i' a au b) | i == i' -> do
    ann <- case ann of
      Just ann -> do
        ann <- check cxt ann (VU au) Set
        unifyTypes cxt (eval cxt ann) a
        pure ann
      Nothing ->
        pure $ quote cxt a
    let x'' = pick x x'
    t <- check (bind x'' NOSource a au cxt) t (b (VVar (cxt^.len))) topU
    pure $ Lam x'' i ann au t

  (t, VPi x Impl a au b) -> do
    t <- check (bind x NOInserted a au cxt) t (b (VVar (cxt^.len))) topU
    pure $ Lam x Impl (quote cxt a) au t

  (RPair t u, VSg x a au b bu) -> do
    t <- check cxt t a au
    u <- check cxt u (b (eval cxt t)) bu
    pure (Pair t au u bu)

  (RLet x a t u, _) -> do
    (a, au) <- inferTy cxt a
    let ~va = eval cxt a
    t <- check cxt t va au
    let ~vt = eval cxt t
    u <- check (define x va au vt cxt) u topA topU
    pure $ Let x a au t u

  (RHole, _) -> do
    freshMeta cxt topA topU

  -- special case for saturated coe
  (RAppE (unSrc -> RAppE (unSrc -> RCoe) p) t, _) -> do
    (t, va, au) <- insert cxt $ infer cxt t
    unifyTypes cxt (VU au) (VU topU)
    p <- checkEq cxt p (VU au) va topA
    -- p <- check cxt p (vEq cxt (VU au) va topA) Prop
    pure (tCoe au (quote cxt va) (quote cxt topA) p t)

  (t, _) -> do
    (t, va, au) <- insert cxt $ infer cxt t
    -- traceShowM ("inferred", showTm' cxt t, showVal cxt va, forceU au)
    unifyTypes cxt (VU au) (VU topU)
    -- traceShowM ("unifyWhile", forceU au, showVal cxt va, showVal cxt topA)
    unifyTypes cxt va topA
    pure t

-- | We specialcase top-level lambdas (serving as postulates) for better
--   printing: we don't print them in meta spines.
inferTopLams :: Cxt -> Raw -> IO (Tm, VTy, U)
inferTopLams cxt = \case
  RLam x ann i t -> do
    (a, au) <- case ann of
      Just ann -> inferTy cxt ann
      Nothing  -> newTy cxt
    let ~va = eval cxt a
    (t, liftVal cxt -> b, bu) <- inferTopLams (bind ('*':x) NOSource va au cxt) t
    pure (Lam x i a au t, VPi x i va au b, bu)
  RSrcPos p t ->
    addSrcPos p $ inferTopLams cxt t

  t -> infer cxt t

infer :: Cxt -> Raw -> IO (Tm, VTy, U)
infer cxt = \case
  RSrcPos p t -> addSrcPos p $ infer cxt t

  RSet  -> pure (U Set , VSet, Set)
  RProp -> pure (U Prop, VSet, Set)

  RVar x -> do
    let go :: [Name] -> [NameOrigin] -> Types -> Int -> IO (Tm, VTy, U)
        go (y:xs) (NOSource:os) (TSnoc _  a un) i | x == y || ('*':x) == y =
          pure (Var i, a, un)
        go (_:xs) (_       :os) (TSnoc as _ _)  i =
          go xs os as (i + 1)
        go []     []            TNil            _ =
          report cxt (NameNotInScope x)
        go _ _ _ _ = error "impossible"
    go (cxt^.names) (cxt^.nameOrigin) (cxt^.types) 0

  RSg x a b -> do
    (a, au) <- inferTy cxt a
    let ~va = eval cxt a
    (b, bu) <- inferTy (bind x NOSource va au cxt) b
    pure (Sg x a au b bu, VU (au <> bu), Set)

  RPair t u -> do -- we only try to infer non-dependent Sg
    (t, a, au) <- infer cxt t
    (u, b, bu) <- infer cxt u
    pure (Pair t au u bu, VSg "_" a au (const b) bu, au <> bu)

  RAppE (unSrc -> RProj1) t -> do
    (t, sg, sgu) <- infer cxt t
    case unglue (force cxt sg) of
      VSg x a au b bu -> pure (Proj1 t sgu, a, au)
      sg              -> report cxt $ ExpectedSg (quote cxt sg)

  RAppE (unSrc -> RProj2) t -> do
    (t, sg, sgu) <- infer cxt t
    let ~vt = eval cxt t
    case unglue (force cxt sg) of
      VSg x a au b bu -> pure (Proj2 t sgu, b (vProj1 vt sgu), bu)
      sg              -> report cxt $ ExpectedSg (quote cxt sg)

  RProj1 -> report cxt UnappliedProj
  RProj2 -> report cxt UnappliedProj

  RPi x i a b -> do
    (a, au) <- inferTy cxt a
    let ~va = eval cxt a
    (b, bu) <- inferTy (bind x NOSource va au cxt) b
    pure (Pi x i a au b, VU bu, Set)

  RApp t u i -> do
    (t, topA, topU) <- case i of Expl -> insert cxt $ infer cxt t
                                 _    -> infer cxt t
    case unglue (force cxt topA) of
      VPi x i' a au b -> do
        unless (i == i') $
          report cxt $ IcitMismatch i i'
        u <- check cxt u a au
        pure (App t u au i, b (eval cxt u), topU)
      VNe (HMeta m) sp -> do
        (a, au) <- newTy cxt
        let ~av = eval cxt a
        (b, bu) <- newTy (bind "x" NOInserted av au cxt)
        let bv ~x = Eval.eval (VDef (cxt^.vals) x) (cxt^.len + 1) b
        unifyTypes cxt (VU bu) (VU topU)
        unifyTypes cxt (VNe (HMeta m) sp) (VPi "x" i av au bv)
        u <- check cxt u av au
        pure (App t u au i, bv (eval cxt u), bu)
      _ ->
        report cxt $ ExpectedFunction (quote cxt topA)

  RLam x ann i t -> do
    (a, au) <- case ann of
      Just ann -> inferTy cxt ann
      Nothing  -> newTy cxt
    let ~va = eval cxt a
    (t, liftVal cxt -> b, bu) <- infer (bind x NOSource va au cxt) t
    pure (Lam x i a au t, VPi x i va au b, bu)

  RHole -> do
    (a, au) <- newTy cxt
    let ~av = eval cxt a
    t <- freshMeta cxt av au
    pure (t, av, au)

  RLet x a t u -> do
    (a, au) <- inferTy cxt a
    let ~va = eval cxt a
    t <- check cxt t va au
    let ~vt = eval cxt t
    (u, b, bu) <- infer (define x va au vt cxt) u
    pure (Let x a au t u, b, bu)

  RTop -> pure (Top, VProp, Set)
  RTt  -> pure (Tt,  VTop,  Prop)
  RBot -> pure (Bot, VProp, Set)

  RExfalso -> do
    u <- UMeta <$> newU
    let ty = VPiIS "A" (VU u) \ ~a -> VPiEP "p" VBot \ ~p -> a
    pure (Exfalso u, ty, u)

  REq -> do
    let ty = VPiIS "A" VSet \ ~a -> VPiES "x" a \ ~x -> VPiES "y" a \ ~y -> VProp
    pure (Eq, ty, Set)

  RRefl -> do
    let ty = VPiIS "A" VSet \ ~a -> VPiIS "x" a \ ~x -> vEq cxt a x x
    pure (Refl, ty, Prop)

  RCoe -> do
    u <- UMeta <$> newU
    let ty = VPiIS "A" (VU u) \ ~a -> VPiIS "B" (VU u) \ ~b ->
             VPiEP "p" (vEq cxt (VU u) a b) \ ~p -> VPi "t" Expl a u \ ~_ -> b
    pure (Coe u, ty, u)

  RSym -> do
    let ty = VPiIS "A" VSet \ ~a -> VPiIS "x" a \ ~x ->
             VPiIS "y" a \ ~y -> VPiEP "p" (vEq cxt a x y) \ ~p -> vEq cxt a y x
    pure (Sym, ty, Prop)

  RTrans -> do
    let ty = VPiIS "A" VSet \ ~a -> VPiIS "x" a \ ~x ->
             VPiIS "y" a \ ~y -> VPiIS "z" a \ ~z ->
             VPiEP "p" (vEq cxt a x y) \ ~p -> VPiEP "q" (vEq cxt a y z) \ ~q ->
             vEq cxt a x z
    pure (Trans, ty, Prop)

  RAp -> do
    let ty = VPiIS "A" VSet \ ~a -> VPiIS "B" VSet \ ~b ->
             VPiES "f" (VPiES "_" a (const b)) \ ~f -> VPiIS "x" a \ ~x ->
             VPiIS "y" a \ ~y -> VPiEP "p" (vEq cxt a x y) \ ~p ->
             vEq cxt b (vApp f x Set Expl) (vApp f y Set Expl)
    pure (Ap, ty, Prop)
