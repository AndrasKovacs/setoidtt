
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Elaboration where

{-|

Current design:
- eval is purely syntax-directed
- unif if universe-directed, but not type-directed
- Prop is not a subtype of Set
- ⊤ and ⊥ are in Prop, Π and Σ are universe-polymorphic
- exfalso and coe are univ-polymorphic in target



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
import Evaluation
import ElabState
import Errors
import Pretty

import Debug.Trace

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
liftVal cxt t ~x = eval (VDef (cxt^.vals) x) $ quote (cxt^.len+1) t

-- Unification
--------------------------------------------------------------------------------

-- | Checks that a spine consists only of distinct bound vars.
--   Returns a partial variable renaming on success, alongside the size
--   of the spine, and the list of variables in the spine.
--   May throw SpineError.
checkSp :: Spine -> IO (Renaming, Lvl, [Lvl])
checkSp = (over _3 reverse <$>) . go where
  go :: Spine -> IO (Renaming, Lvl, [Lvl])
  go = \case
    SNil           -> pure (mempty, 0, [])
    SApp sp u un i -> do
      (!r, !d, !xs) <- go sp
      case force u of
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
    go tys ns (d-1) (Pi x Expl (quote (d-1) a) au b)
  go _                     _      _ _ = error "impossible"

-- | Close a term by wrapping it in `Int` number of lambdas, while taking the domain
--   types from the `VTy`, and the binder names from a list. If we run out of provided
--   binder names, we pick the names from Pi domains.
closingTm :: (VTy, Int, [Name]) -> Tm -> Tm
closingTm = go 0 where
  getName []     x = x
  getName (x:xs) _ = x

  go d (a, 0, _)   rhs = rhs
  go d (a, len, xs) rhs = case force a of
    VPi (getName xs -> x) i a au b  ->
      Lam x i (quote d a) au $
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
              go (True:pr) str (force -> VPi x i a au b) =
                Pi x i <$> strengthen rel str a <*> pure au <*>
                      go pr (liftStr str) (b (VVar (str^.cod)))
              go (False:pr) str (force -> VPi x i a un b) =
                go pr (skipStr str) (b (VVar (str^.cod)))
              go _ _ _ = error "impossible"

          go pruning (Str 0 0 mempty Nothing) metaTy

        m' <- newMeta (eval VNil prunedTy) metaU

        let argNum = length pruning
            body = go pruning metaTy (Meta m') 0 where
              go :: [Bool] -> VTy -> _ -> _
              go [] a acc d = acc
              go (True:pr) (force -> VPi x i a au b) acc d =
                go pr (b (VVar d))
                      (App acc (Var (argNum - d - 1)) au i) (d + 1)
              go (False:pr) (force -> VPi x i a au b) acc d =
                go pr (b (VVar d)) acc (d + 1)
              go _ _ _ _ = error "impossible"

        let rhs = closingTm (metaTy, argNum, []) body
        writeMeta m $ Solved (eval VNil rhs)

  go t = case force t of
    VNe (HVar x) sp         -> case IM.lookup x (str^.ren) of
                                 Nothing -> throwIO $ ScopeError x
                                 Just x' -> goSp (Var (str^.dom - x' - 1)) sp
    VNe (HMeta m) sp        -> if Just m == str^.occ then
                                 throwIO OccursCheck
                               else do
                                 prune m sp
                                 case force (VNe (HMeta m) sp) of
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
  let ~topLhs = quote (cxt^.len) (VNe (HMeta m) sp)
      ~topRhs = quote (cxt^.len) rhs

  (ren, spLen, spVars) <- checkSp sp
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
  writeMeta m (Solved (eval VNil closedRhs))

freshMeta :: Cxt -> VTy -> U -> IO Tm
freshMeta cxt (quote (cxt^.len) -> a) au = do
  let metaTy = closingTy cxt a
  m <- newMeta (eval VNil metaTy) au

  let vars :: Types -> (Spine, Lvl)
      vars TNil                              = (SNil, 0)
      vars (TDef (vars -> (sp, !d)) _ _)     = (sp, d + 1)
      vars (TBound (vars -> (sp, !d)) _ un)  = (SApp sp (VVar d) un Expl, d + 1)

  let sp = fst $ vars (cxt^.types)
  pure (quote (cxt^.len) (VNe (HMeta m) sp))

unifyTypes :: Cxt -> Val -> Val -> IO ()
unifyTypes cxt l r =
  unify Relevant cxt Set l r
  `catch`
  (report (cxt^.names) . UnifyErrorWhile (quote (cxt^.len) l) (quote (cxt^.len) r))

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
    throwIO $ UnifyError (cxt^.names) (quote (cxt^.len) l) (quote (cxt^.len) r)

  go :: U -> Val -> Val -> IO ()
  go un t t' = case (rel, forceU un) of
    (Relevant, Prop) -> do
      unify Irrelevant cxt un t t' `catch` \(e :: UnifyError) -> pure ()

    _ -> case (force t, force t') of
      (VLam x _ a au t, VLam x' _ _ _ t') -> goBind (pickName x x') a au un t t'
      (VLam x i a au t, t')               -> goBind x a au un t (\ ~v -> vApp t' v au i)
      (t, VLam x' i' a' au' t')           -> goBind x' a' au' un (\ ~v -> vApp t v au' i') t'

      (VPi x i a au b, VPi x' i' a' au' b') | i == i' -> do
        goU au au'
        go Set a a'
        goBind (pickName x x') a au Set b b'

      (VSg x a au b bu, VSg x' a' au' b' bu') -> do
        goU au au'  >> goU bu bu'
        go Set a a' >> goBind (pickName x x') a au Set b b'

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


      -- TODO: rigidity check
      (VEq a x y, VEq a' x' y') -> go Set a a' >> go Set x x' >> go Set y y'

      (VNe h sp, VNe h' sp') -> case (h, h') of

        (HVar x, HVar x') | x == x' -> goSp  sp sp'
        (HAxiom ax, HAxiom ax') -> case (ax, ax') of

          (ARfl, ARfl)              -> goSp sp sp'
          (ASym, ASym)              -> goSp sp sp'
          (AAp , AAp )              -> goSp sp sp'
          (AExfalso u, AExfalso u') -> goU u u' >> goSp sp sp'
          _                         -> err t t'

        (HCoe u a b p t, HCoe u' a' b' p' t') -> do
          goU u u' >> go Set a a' >> go Set b b' >> go Prop p p' >> go u t t'

        (HMeta m, HMeta m') | m == m'   -> goSp sp sp'
                            | otherwise -> try @SpineError (checkSp sp) >>= \case
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

  goSp :: Spine -> Spine -> IO ()
  goSp sp sp' = case (sp, sp') of
    (SNil, SNil)                                   -> pure ()
    (SApp sp u uu i, SApp sp' u' uu' i') | i == i' -> goSp sp sp' >>
                                                      goU uu uu' >> go uu u u'
    _                                              -> error "impossible"



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
      go t va = case force va of
        VPi x Impl a au b -> do
          m <- freshMeta cxt a au
          let mv = eval (cxt^.vals) m
          go (App t m au Impl) (b mv)
        va -> pure (t, va)
  (a, va) <- go t va
  pure (a, va, un)

inferTy :: Cxt -> Raw -> IO (Tm, U)
inferTy cxt a = do
  (a, au, _) <- infer cxt a
  au <- case force au of
    VSet                 -> pure Set
    VProp                -> pure Prop
    VU (UMeta x)         -> pure (UMeta x)
    au@(VNe (HMeta{}) _) -> do
      u <- UMeta <$> newU
      unifyTypes cxt au (VU u)
      pure u
    au -> report (cxt^.names) $ ExpectedType a (quote (cxt^.len) au)
  pure (a, au)

-- | Choose the more informative name.
pickName :: Name -> Name -> Name
pickName "_" x  = x
pickName x  "_" = x
pickName x  y   = x

check :: Cxt -> Raw -> VTy -> U -> IO Tm
check cxt topT ~topA ~topU = case (topT, force topA) of
  (RSrcPos p t, a) ->
    addSrcPos p (check cxt t a topU)

  (RLam x ann i t, VPi x' i' a au b) | i == i' -> do
    ann <- case ann of
      Just ann -> do
        ann <- check cxt ann (VU au) Set
        unifyTypes cxt (eval (cxt^.vals) ann) a
        pure ann
      Nothing ->
        pure $ quote (cxt^.len) a
    let x'' = pickName x x'
    t <- check (bind x'' NOSource a au cxt) t (b (VVar (cxt^.len))) topU
    pure $ Lam x'' i ann au t

  (t, VPi x Impl a au b) -> do
    t <- check (bind x NOInserted a au cxt) t (b (VVar (cxt^.len))) topU
    pure $ Lam x Impl (quote (cxt^.len) a) au t

  (RPair t u, VSg x a au b bu) -> do
    t <- check cxt t a au
    u <- check cxt u (b (eval (cxt^.vals) t)) bu
    pure (Pair t au u bu)

  (RLet x a t u, topA) -> do
    (a, au) <- inferTy cxt a
    let ~va = eval (cxt^.vals) a
    t <- check cxt t va au
    let ~vt = eval (cxt^.vals) t
    u <- check (define x va au vt cxt) u topA topU
    pure $ Let x a au t u

  (RHole, topA) -> do
    freshMeta cxt topA topU

  (t, topA) -> do
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
    let ~va = eval (cxt^.vals) a
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
          report (cxt^.names) (NameNotInScope x)
        go _ _ _ _ = error "impossible"
    go (cxt^.names) (cxt^.nameOrigin) (cxt^.types) 0

  RPi x i a b -> do
    (a, au) <- inferTy cxt a
    let ~va = eval (cxt^.vals) a
    (b, bu) <- inferTy (bind x NOSource va au cxt) b
    pure (Pi x i a au b, VU bu, Set)

  RApp t u i -> do
    (t, topA, topU) <- case i of Expl -> insert cxt $ infer cxt t
                                 _    -> infer cxt t
    case force topA of
      VPi x i' a au b -> do
        unless (i == i') $
          report (cxt^.names) $ IcitMismatch i i'
        u <- check cxt u a au
        pure (App t u au i, b (eval (cxt^.vals) u), topU)
      VNe (HMeta m) sp -> do
        (a, au) <- newTy cxt
        let ~av = eval (cxt^.vals) a
        (b, bu) <- newTy (bind "x" NOInserted av au cxt)
        let bv ~x = eval (VDef (cxt^.vals) x) b
        unifyTypes cxt (VNe (HMeta m) sp) (VPi "x" i av au bv)
        u <- check cxt u av au
        pure (App t u au i, bv (eval (cxt^.vals) u), bu)
      _ ->
        report (cxt^.names) $ ExpectedFunction (quote (cxt^.len) topA)

  RLam x ann i t -> do
    (a, au) <- case ann of
      Just ann -> inferTy cxt ann
      Nothing  -> newTy cxt
    let ~va = eval (cxt^.vals) a
    (t, liftVal cxt -> b, bu) <- infer (bind x NOSource va au cxt) t
    pure (Lam x i a au t, VPi x i va au b, bu)

  RHole -> do
    (a, au) <- newTy cxt
    let ~av = eval (cxt^.vals) a
    t <- freshMeta cxt av au
    pure (t, av, au)

  RLet x a t u -> do
    (a, au) <- inferTy cxt a
    let ~va = eval (cxt^.vals) a
    t <- check cxt t va au
    let ~vt = eval (cxt^.vals) t
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

  RRfl -> do
    let ty = VPiIS "A" VSet \ ~a -> VPiIS "x" a \ ~x -> VEq a x x
    pure (Rfl, ty, Prop)

  RCoe -> do
    u <- UMeta <$> newU
    let ty = VPiIS "A" (VU u) \ ~a -> VPiIS "B" (VU u) \ ~b ->
             VPiEP "p" (VEq (VU u) a b) \ ~p -> VPi "t" Expl a u \ ~_ -> b
    pure (Coe u, ty, u)

  RSym -> do
    let ty = VPiIS "A" VSet \ ~a -> VPiIS "x" a \ ~x ->
             VPiIS "y" a \ ~y -> VPiEP "p" (VEq a x y) \ ~p -> VEq a y x
    pure (Sym, ty, Prop)

  RAp -> do
    let ty = VPiIS "A" VSet \ ~a -> VPiIS "B" VSet \ ~b ->
             VPiES "f" (VPiES "_" a (const b)) \ ~f -> VPiIS "x" a \ ~x ->
             VPiIS "y" a \ ~y -> VPiEP "p" (VEq a x y) \ ~p ->
             VEq b (vApp f x Set Expl) (vApp f y Set Expl)
    pure (Ap, ty, Prop)

  RSg x a b -> do
    (a, au) <- inferTy cxt a
    let ~va = eval (cxt^.vals) a
    (b, bu) <- inferTy (bind x NOSource va au cxt) b
    pure (Sg x a au b bu, VU (au <> bu), Set)

  -- we only try to infer non-dependent Sg
  RPair t u -> do
    (t, a, au) <- infer cxt t
    (u, b, bu) <- infer cxt u
    pure (Pair t au u bu, VSg "_" a au (const b) bu, au <> bu)

  RProj1 t -> do
    (t, sg, sgu) <- infer cxt t
    case force sg of
      VSg x a au b bu -> pure (Proj1 t sgu, a, au)
      sg              -> report (cxt^.names) $ ExpectedSg (quote (cxt^.len) sg)

  RProj2 t -> do
    (t, sg, sgu) <- infer cxt t
    let ~vt = eval (cxt^.vals) t
    case force sg of
      VSg x a au b bu -> pure (Proj2 t sgu, b (vProj1 vt sgu), bu)
      sg              -> report (cxt^.names) $ ExpectedSg (quote (cxt^.len) sg)
