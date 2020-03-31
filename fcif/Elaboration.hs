
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
import qualified Data.IntMap as IM

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

-- | Strengthens a value, returns a quoted normal result. This performs scope
--   checking, meta occurs checking and (recursive) pruning at the same time.
--   May throw StrengtheningError.
strengthen :: Str -> Val -> IO Tm
strengthen str = go where

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

        -- note: this can cause recursive pruning of metas in types
        (prunedTy :: Ty) <- do
          let go :: [Bool] -> Str -> VTy -> IO Ty
              go [] str a = strengthen str a
              go (True:pr) str (force -> VPi x i a au b) =
                Pi x i <$> strengthen str a <*> pure au <*>
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
    VNe (HVar x) sp  -> case IM.lookup x (str^.ren) of
                          Nothing -> throwIO $ ScopeError x
                          Just x' -> goSp (Var (str^.dom - x' - 1)) sp
    VNe (HMeta m) sp -> if Just m == str^.occ then
                          throwIO OccursCheck
                        else do
                          prune m sp
                          case force (VNe (HMeta m) sp) of
                            VNe (HMeta m) sp -> goSp (Meta m) sp
                            _                -> error "impossible"

    VPi x i a au b   -> Pi x i <$> go a <*> pure au <*> goBind b
    VLam x i a au t  -> Lam x i <$> go a <*> pure au <*> goBind t
    VU u             -> pure (U u)
    VTop             -> pure Top
    VTt              -> pure Tt
    VBot             -> pure Bot
    VExfalso u a t   -> Exfalso' u <$> go a <*> go t
    VEq a x y        -> Eq' <$> go a <*> go x <*> go y
    VRfl a x         -> Rfl' <$> go a <*> go x
    VCoe u a b p t   -> Coe' u <$> go a <*> go b <*> go p <*> go t
    VSym a x y p     -> Sym' <$> go a <*> go x <*> go y <*> go p
    VAp a b f x y p  -> Ap' <$> go a <*> go b <*> go f <*> go x <*> go y <*> go p

  goBind t = strengthen (liftStr str) (t (VVar (str^.cod)))

  goSp h = \case
    SNil           -> pure h
    SApp sp u uu i -> App <$> goSp h sp <*> go u <*> pure uu <*> pure i

-- | May throw UnifyError.
solveMeta :: Cxt -> MId -> Spine -> Val -> IO ()
solveMeta cxt m sp rhs = do

  -- these normal forms are only used in error reporting
  let ~topLhs = quote (cxt^.len) (VNe (HMeta m) sp)
      ~topRhs = quote (cxt^.len) rhs

  -- ISSUE: we would need to backtrack the prunings and meta lookups here,
  -- if we fail solution while having irrelevant rhs!
  -- Currently we simply fail here, even though possibly some other equation
  -- may solve irrelevant metas!
  (ren, spLen, spVars) <- checkSp sp
         `catch` (throwIO . SpineError (cxt^.names) topLhs topRhs)
  rhs <- strengthen (Str spLen (cxt^.len) ren (Just m)) rhs
         `catch` (throwIO . StrengtheningError (cxt^.names) topLhs topRhs)

  (metaTy, metaU) <- lookupMeta m >>= \case
    Unsolved a au -> pure (a, au)
    _             -> error "impossible"

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

unifyWhile cxt un l r =
  unify cxt un l r
  `catch`
  (report (cxt^.names) . UnifyErrorWhile (quote (cxt^.len) l) (quote (cxt^.len) r))

-- subsumeWhile cxt un l r =
--   subsume cxt un l r
--   `catch`
--   (report (cxt^.names) . SubsumptionErrorWhile (quote (cxt^.len) l) (quote (cxt^.len) r))

solveU :: UId -> U -> IO ()
solveU x u = writeU x (Just u)

unifyU :: U -> U -> IO ()
unifyU u u' = case (forceU u, forceU u') of
  (Prop,    Prop    )           -> pure ()
  (Set,     Set     )           -> pure ()
  (UMeta x, UMeta x') | x == x' -> pure ()
  (UMeta x, u       )           -> solveU x u
  (u,       UMeta x )           -> solveU x u
  (u,       u'      )           -> throwIO $ UnifyError [] (U u) (U u')

-- -- | subsume : (u : U) -> Ty u -> Ty u -> IO ()
-- subsume :: Cxt -> U -> VTy -> VTy -> IO ()
-- subsume cxt u l r = case forceU u of
--   Set -> case (force l, force r) of
--     (VU u, VU u') -> case (forceU u, forceU u') of
--       (Prop, Set) -> pure ()
--       (u   , u' ) -> unifyU u u'
--     (VPi x i a au b, VPi x' i' a' au' b') -> do
--       unifyU au au'
--       unify cxt au a a'
--       let v = VVar (cxt^.len)
--       subsume (bindSrc x a au cxt) Set (b v) (b' v)
--     (l, r) -> unify cxt Set l r
--   _ -> unify cxt u l r

-- | May throw UnifyError.
unify :: Cxt -> U -> Val -> Val -> IO ()
unify cxt un l r = go un l r where

  unifyError =
    throwIO $ UnifyError (cxt^.names) (quote (cxt^.len) l) (quote (cxt^.len) r)

  flexFlex m sp m' sp' = do
    try @SpineError (checkSp sp) >>= \case
      Left{}  -> solveMeta cxt m' sp' (VNe (HMeta m) sp)
      Right{} -> solveMeta cxt m sp (VNe (HMeta m') sp')

  go :: U -> Val -> Val -> IO ()
  go un t t' = case (force t, force t') of
    (VLam x _ a au t, VLam _ _ _ _ t')       -> goBind x a au un t t'
    (VLam x i a au t, t')                    -> goBind x a au un t (\ ~v -> vApp t' v au i)
    (t, VLam x' i' a' au' t')                -> goBind x' a' au' un (\ ~v -> vApp t v au' i') t'
    (VPi x i a au b,
       VPi x' i' a' au' b') | i == i'        -> unifyU au au' >>
                                                go Set a a' >> goBind x a au Set b b'
    (VU u, VU u')                            -> unifyU u u'
    (VTop, VTop)                             -> pure ()
    (VTt, VTt)                               -> pure ()
    (VBot, VBot)                             -> pure ()
    (VExfalso _ a t, VExfalso _ a' t')       -> go Set a a' >> go Prop t t'
    (VEq a x y, VEq a' x' y')                -> go Set a a' >> go Set x x' >> go Set y y'
    (VRfl a x, VRfl a' x')                   -> go Set a a' >> go Set x x'
    (VSym a x y p, VSym a' x' y' p')         -> go Set a a' >> go Set x x' >> go Set y y'
                                                >> go Prop p p'
    (VCoe u a b p t, VCoe u' a' b' p' t')    -> unifyU u u' >> go Set a a' >> go Set b b' >> go Prop p p'
                                                >> go un t t'
    (VAp a b f x y p, VAp a' b' f' x' y' p') -> go Set a a' >> go Set b b' >> go Set f f'
                                                >> go Set x x' >> go Set y y' >> go Prop p p'
    (VNe h sp, VNe h' sp') | h == h'         -> goSp sp sp'
    (VNe (HMeta m) sp, VNe (HMeta m') sp')   -> flexFlex m sp m' sp'
    (VNe (HMeta m) sp, t')                   -> solveMeta cxt m sp t'
    (t, VNe (HMeta m') sp')                  -> solveMeta cxt m' sp' t
    _                                        -> case forceU un of
                                                  Prop -> pure ()
                                                  _    -> unifyError

  goBind :: Name -> VTy -> U -> U -> (Val -> Val) -> (Val -> Val) -> IO ()
  goBind x a au un t t' =
    let v = VVar (cxt^.len) in unify (bindSrc x a au cxt) un (t v) (t' v)

  goSp :: Spine -> Spine -> IO ()
  goSp sp sp' = case (sp, sp') of
    (SNil, SNil)                                   -> pure ()
    (SApp sp u uu i, SApp sp' u' uu' i') | i == i' -> goSp sp sp' >>
                                                      unifyU uu uu' >> go uu u u'
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
      unifyWhile cxt Set au (VU u)
      pure u
    au -> report (cxt^.names) $ ExpectedType a (quote (cxt^.len) au)
  pure (a, au)

check :: Cxt -> Raw -> VTy -> U -> IO Tm
check cxt topT ~topA ~topU = case (topT, force topA) of
  (RSrcPos p t, a) ->
    addSrcPos p (check cxt t a topU)

  (RLam x ann i t, VPi x' i' a au b) | i == i' -> do
    ann <- case ann of
      Just ann -> do
        ann <- check cxt ann (VU au) Set
        unifyWhile cxt au (eval (cxt^.vals) ann) a
        pure ann
      Nothing ->
        pure $ quote (cxt^.len) a
    t <- check (bind x NOSource a au cxt) t (b (VVar (cxt^.len))) topU
    pure $ Lam x i ann au t

  (t, VPi x Impl a au b) -> do
    t <- check (bind x NOInserted a au cxt) t (b (VVar (cxt^.len))) topU
    pure $ Lam x Impl (quote (cxt^.len) a) au t

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
    unifyWhile cxt Set (VU au) (VU topU)
    unifyWhile cxt au va topA
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
        unifyWhile cxt bu (VNe (HMeta m) sp) (VPi "x" i av au bv)
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
             VPiES "f" (vFunES a b) \ ~f -> VPiIS "x" a \ ~x ->
             VPiIS "y" a \ ~y -> VPiEP "p" (VEq a x y) \ ~p ->
             VEq b (vApp f x Set Expl) (vApp f y Set Expl)
    pure (Ap, ty, Prop)
