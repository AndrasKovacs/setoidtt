
module Elaboration where

import Control.Exception
import Control.Monad
import Data.IORef
import Data.Maybe
import Lens.Micro.Platform
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Types
import Evaluation
import ElabState
import Errors

-- Context operations
--------------------------------------------------------------------------------

emptyCxt :: Cxt
emptyCxt = Cxt VNil TNil [] [] 0

-- | Add a bound variable.
bind :: Name -> NameOrigin -> VTy -> VUniv -> Cxt -> Cxt
bind x o ~a ~un (Cxt vs tys ns no d) =
  Cxt (VSkip vs) (TBound tys a un) (x:ns) (o:no) (d + 1)

-- | Add a bound variable which comes from surface syntax.
bindSrc :: Name -> VTy -> VUniv -> Cxt -> Cxt
bindSrc x = bind x NOSource

-- | Define a new variable.
define :: Name -> VTy -> VUniv -> Val -> Cxt -> Cxt
define x ~a ~un ~t (Cxt vs tys ns no d) =
  Cxt (VDef vs t) (TDef tys a un) (x:ns) (NOSource:no) (d + 1)

-- | Lift ("skolemize") a value in an extended context to a function in a
--   non-extended context.
liftVal :: Cxt -> Val -> (Val -> Val)
liftVal cxt t = \ ~x -> eval (VDef (cxt^.vals) x) $ quote (cxt^.len+1) t


-- Constancy constraints
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

-- | Occurs check for the purpose of constraint solving.
occurs :: Lvl -> Lvl -> Val -> Occurs
occurs d topX = occurs' d mempty where

  occurs' :: Lvl -> IS.IntSet -> Val -> Occurs
  occurs' d ms = go where

    goSp ms sp = case forceSp sp of
      SNil           -> mempty
      SApp sp u un i -> goSp ms sp <> go u <> go un

    goBind t =
      occurs' (d + 1) ms (t (VVar d))

    go v = case force v of
      VNe (HVar x) sp | x == topX -> occurrence ms <> goSp ms sp
      VNe (HVar x) sp             -> goSp ms sp
      VNe (HMeta m) sp            -> goSp (IS.insert m ms) sp
      VPi _ i a un b  -> go a <> go un <> goBind b
      VLam _ i a un t -> go a <> go un <> goBind t
      VSet            -> mempty
      VProp           -> mempty

-- Unification
--------------------------------------------------------------------------------

-- | Checks that a spine consists only of distinct bound vars.
--   Returns a partial variable renaming on success, alongside the size
--   of the spine, and the list of variables in the spine.
--   May throw SpineError.
checkSp :: Spine -> IO (Renaming, Lvl, [Lvl])
checkSp = (over _3 reverse <$>) . go . forceSp where
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
  go (TDef tys a un)       (x:ns) d b = go tys ns (d-1) (Skip b)
  go (TBound tys a un)     (x:ns) d b =
    go tys ns (d-1) (Pi x Expl (quote (d-1) a) (quote (d - 1) un) b)
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
    VPi (getName xs -> x) i a un b  ->
      Lam x i (quote d a) (quote d un) $
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
              go (True:pr) str (force -> VPi x i a un b) =
                Pi x i <$> strengthen str a <*> strengthen str un <*>
                      go pr (liftStr str) (b (VVar (str^.cod)))
              go (False:pr) str (force -> VPi x i a un b) =
                go pr (skipStr str) (b (VVar (str^.cod)))
              go _ _ _ = error "impossible"

          go pruning (Str 0 0 mempty Nothing) metaTy

        m' <- newMeta $ Unsolved mempty (eval VNil prunedTy)

        let argNum = length pruning
            body = go pruning metaTy (Meta m') 0 where
              go :: [Bool] -> VTy -> _ -> _
              go [] a acc d = acc
              go (True:pr) (force -> VPi x i a un b) acc d =
                go pr (b (VVar d))
                      (App acc (Var (argNum - d - 1)) (quote argNum un) i) (d + 1)
              go (False:pr) (force -> VPi x i a un b) acc d =
                go pr (b (VVar d)) acc (d + 1)
              go _ _ _ _ = error "impossible"

        let rhs = closingTm (metaTy, argNum, []) body
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

    VPi x i a un b   -> Pi x i <$> go a <*> go un <*> goBind b
    VLam x i a un t  -> Lam x i <$> go a <*> go un <*> goBind t
    VSet             -> pure Set
    VProp            -> pure Prop

  goBind t = strengthen (liftStr str) (t (VVar (str^.cod)))

  goSp h = \case
    SNil           -> pure h
    SApp sp u un i -> App <$> goSp h sp <*> go u <*> go un <*> pure i

-- | May throw UnifyError.
solveMeta :: Cxt -> MId -> Spine -> Val -> IO ()
solveMeta cxt m sp rhs = do

  -- these normal forms are only used in error reporting
  let ~topLhs = quote (cxt^.len) (VNe (HMeta m) sp)
      ~topRhs = quote (cxt^.len) rhs

  (ren, spLen, spVars) <- checkSp sp
         `catch` (throwIO . SpineError (cxt^.names) topLhs topRhs)

  rhs <- strengthen (Str spLen (cxt^.len) ren (Just m)) rhs
         `catch` (throwIO . StrengtheningError (cxt^.names) topLhs topRhs)

  (blocked, metaTy) <- lookupMeta m >>= \case
    Unsolved blocked a -> pure (blocked, a)
    _                  -> error "impossible"

  let spVarNames = map (lvlName (cxt^.names)) spVars
  let closedRhs = closingTm (metaTy, spLen, spVarNames) rhs
  writeMeta m (Solved (eval VNil closedRhs))

freshMeta :: Cxt -> VTy -> IO Tm
freshMeta cxt (quote (cxt^.len) -> a) = do
  let metaTy = closingTy cxt a
  m <- newMeta $ Unsolved mempty (eval VNil metaTy)

  let vars :: Types -> (Spine, Lvl)
      vars TNil                              = (SNil, 0)
      vars (TDef (vars -> (sp, !d)) _ _)     = (sp, d + 1)
      vars (TBound (vars -> (sp, !d)) _ un)  = (SApp sp (VVar d) un Expl, d + 1)

  let sp = fst $ vars (cxt^.types)
  pure (quote (cxt^.len) (VNe (HMeta m) sp))

-- | Wrap the inner UnifyError arising from unification in an UnifyErrorWhile.
unifyWhile :: Cxt -> Val -> Val -> IO ()
unifyWhile cxt l r =
  unify cxt l r
  `catch`
  (report (cxt^.names) . UnifyErrorWhile (quote (cxt^.len) l) (quote (cxt^.len) r))

-- | May throw UnifyError.
unify :: Cxt -> Val -> Val -> IO ()
unify cxt l r = go l r where

  unifyError =
    throwIO $ UnifyError (cxt^.names) (quote (cxt^.len) l) (quote (cxt^.len) r)

  flexFlex m sp m' sp' = do
    try @SpineError (checkSp sp) >>= \case
      Left{}  -> solveMeta cxt m' sp' (VNe (HMeta m) sp)
      Right{} -> solveMeta cxt m sp (VNe (HMeta m') sp')

  go t t' = case (force t, force t') of
    (VLam x _ a un t, VLam _ _ _ _ t')       -> goBind x a un t t'
    (VLam x i a un t, t')                    -> goBind x a un t (\ ~v -> vApp t' v un i)
    (t, VLam x' i' un' a' t')                -> goBind x' a' un' (\ ~v -> vApp t v un' i') t'
    (VPi x i a un b,
       VPi x' i' a' un' b') | i == i'        -> go un un' >> go a a' >> goBind x a un b b'
    (VSet, VSet)                             -> pure ()
    (VProp, VProp)                           -> pure ()
    (VNe h sp, VNe h' sp') | h == h'         -> goSp (forceSp sp) (forceSp sp')
    (VNe (HMeta m) sp, VNe (HMeta m') sp')   -> flexFlex m sp m' sp'
    (VNe (HMeta m) sp, t')                   -> solveMeta cxt m sp t'
    (t, VNe (HMeta m') sp')                  -> solveMeta cxt m' sp' t
    _                                        -> unifyError

  goBind x a un t t' =
    let v = VVar (cxt^.len) in unify (bindSrc x a un cxt) (t v) (t' v)

  -- TODO: forcing spine while unifying
  goSp sp sp' = case (sp, sp') of
    (SNil, SNil)                                -> pure ()
    (SApp sp u _ i, SApp sp' u' _ i') | i == i' -> goSp sp sp' >> go u u'
    _                                           -> error "impossible"


-- Elaboration
--------------------------------------------------------------------------------

insert :: Cxt -> IO (Tm, VTy, VUniv) -> IO (Tm, VTy, VUniv)
insert cxt act = do
  (t, va, un) <- act
  let go :: Tm -> VTy -> IO (Tm, VTy)
      go t va = case force va of
        VPi x Impl a un b -> do
          m <- freshMeta cxt a
          let mv = eval (cxt^.vals) m
          go (App t m (quote (cxt^.len) un) Impl) (b mv)
        va -> pure (t, va)
  (a, va) <- go t va
  pure (a, va, un)

checkTy :: Cxt -> Raw -> IO (Tm, VUniv)
checkTy cxt a = do
  (a, un, _) <- infer cxt a
  case un of
    VSet  -> pure ()
    VProp -> pure ()
    _     -> report (cxt^.names) $ ExpectedType a (quote (cxt^.len) un)
  pure (a, un)

check :: Cxt -> Raw -> VTy -> IO Tm
check cxt topT ~topA = case (topT, force topA) of
  (RSrcPos p t, a) ->
    addSrcPos p (check cxt t a)

  (RLam x ann i t, VPi x' i' a un b) | i == i' -> do
    ann <- case ann of
      Just ann -> do
        ann <- check cxt ann un
        unifyWhile cxt (eval (cxt^.vals) ann) a
        pure ann
      Nothing ->
        pure $ quote (cxt^.len) a
    t <- check (bind x NOSource a un cxt) t (b (VVar (cxt^.len)))
    pure $ Lam x i ann (quote (cxt^.len) un) t

  (t, VPi x Impl a un b) -> do
    t <- check (bind x NOInserted a un cxt) t (b (VVar (cxt^.len)))
    pure $ Lam x Impl (quote (cxt^.len) a) (quote (cxt^.len) un) t

  (RLet x a t u, topA) -> do
    (a, un) <- checkTy cxt a
    let ~va = eval (cxt^.vals) a
    t <- check cxt t va
    let ~vt = eval (cxt^.vals) t
    u <- check (define x va un vt cxt) u topA
    pure $ Let x a (quote (cxt^.len) un) t u

  (RHole, topA) -> do
    freshMeta cxt topA

  (t, topA) -> do
    (t, va, un) <- insert cxt $ infer cxt t
    unifyWhile cxt va topA
    pure t

-- | We specialcase top-level lambdas (serving as postulates) for better
--   printing: we don't print them in meta spines.
inferTopLams :: Cxt -> Raw -> IO (Tm, VTy, VUniv)
inferTopLams cxt = \case
  RLam x ann i t -> do
    (a, un) <- case ann of
      Just ann -> checkTy cxt ann
      Nothing  -> do
        un <- eval (cxt^.vals) <$> freshMeta cxt VSet
        a <- freshMeta cxt un
        pure (a, un)
    let ~va = eval (cxt^.vals) a
    (t, liftVal cxt -> b, un') <- inferTopLams (bind ('*':x) NOSource va un cxt) t
    pure (Lam x i a (quote (cxt^.len) un) t, VPi x i va un b, un')
  RSrcPos p t ->
    addSrcPos p $ inferTopLams cxt t

  t -> insert cxt $ infer cxt t

infer :: Cxt -> Raw -> IO (Tm, VTy, VUniv)
infer cxt = \case
  RSrcPos p t -> addSrcPos p $ infer cxt t

  RU -> pure (Set, VSet, VSet)

  -- RVar x -> do
  --   let go :: [Name] -> [NameOrigin] -> Types -> Int -> IO (Tm, VTy)
  --       go (y:xs) (NOSource:os) (TSnoc _  a _) i | x == y || ('*':x) == y = pure (Var i, a)
  --       go (_:xs) (_       :os) (TSnoc as _ _) i = go xs os as (i + 1)
  --       go []     []            TNil           _ = report (cxt^.names) (NameNotInScope x)
  --       go _ _ _ _ = error "impossible"
  --   go (cxt^.names) (cxt^.nameOrigin) (cxt^.types) 0

  -- RPi x i a b -> do
  --   a <- check cxt a VU
  --   let ~va = eval (cxt^.vals) a
  --   b <- check (bind x NOSource va _ cxt) b VU
  --   pure (Pi x i a _ b, VU)

  -- -- variant with better error messages and fewer generated metavariables
  -- RApp t u i -> do
  --   (t, va) <- case i of Expl -> insert cxt $ infer cxt t
  --                        _    -> infer cxt t
  --   case force va of
  --     VPi x i' a un b -> do
  --       unless (i == i') $
  --         report (cxt^.names) $ IcitMismatch i i'
  --       u <- check cxt u a
  --       pure (App t u _ i, b (eval (cxt^.vals) u))
  --     VNe (HMeta m) sp -> do
  --       a    <- eval (cxt^.vals) <$> freshMeta cxt VU
  --       cod  <- freshMeta (bind "x" NOInserted a _ cxt) VU
  --       let b ~x = eval (VDef (cxt^.vals) x) cod
  --       unifyWhile cxt (VNe (HMeta m) sp) (VPi "x" i a _ b)
  --       u <- check cxt u a
  --       pure (App t u _ i, b (eval (cxt^.vals) u))
  --     _ ->
  --       report (cxt^.names) $ ExpectedFunction (quote (cxt^.len) va)

  -- RLam x ann i t -> do
  --   a <- case ann of
  --     Just ann -> check cxt ann VU
  --     Nothing  -> freshMeta cxt VU
  --   let ~va = eval (cxt^.vals) a
  --   let cxt' = bind x NOSource va _ cxt
  --   (t, liftVal cxt -> b) <- insert cxt' $ infer cxt' t
  --   pure (Lam x i a t, VPi x i va _ b)

  -- RHole -> do
  --   a <- freshMeta cxt VU
  --   let ~va = eval (cxt^.vals) a
  --   t <- freshMeta cxt va
  --   pure (t, va)

  -- RLet x a t u -> do
  --   a <- check cxt a VU
  --   let ~va = eval (cxt^.vals) a
  --   t <- check cxt t va
  --   let ~vt = eval (cxt^.vals) t
  --   (u, b) <- infer (define x va _ vt cxt) u
  --   pure (Let x a _ t u, b)
