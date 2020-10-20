{-# options_ghc -Wno-unused-imports #-}

module Elaboration (infer, check, bind2Name, insert, insert') where

import Control.Monad

import qualified Data.ByteString     as B
import qualified Data.HashMap.Strict as HM
import qualified Syntax              as S
import qualified Values              as V
import qualified Presyntax           as P
import qualified FlatParse           as FP
import qualified Evaluation          as Eval

import Common
import ElabState
import Exceptions
import Cxt
import EvalInCxt

import Unification hiding (unifySet)
import qualified Unification


{- CORE INSPECTION:
- MYSTERIOUS ISSUE: if I make RawName strict in Cxt, check fails to unbox!
   - MYSTERY SOLVED: it would go over the limit of max worker args!
   - -fmax-worker-args=15    for the rescue!!!!
- HashMap could be improved
- RawString would be nicer in latest ByteString version (3 words)
-}

--------------------------------------------------------------------------------

span2RawName :: Cxt -> Span -> RawName
span2RawName cxt span = RawName (FP.unsafeSpan2ByteString (unRawName (_src cxt)) span)
{-# inline span2RawName #-}

span2Name :: Cxt -> Span -> Name
span2Name cxt = NName . span2RawName cxt
{-# inline span2Name #-}

bind2Name :: Cxt -> P.Bind -> Name
bind2Name cxt (P.Bind x) = NName (span2RawName cxt x)
bind2Name cxt P.DontBind = NEmpty
{-# inline bind2Name #-}

--------------------------------------------------------------------------------

elabError :: Cxt -> P.Tm -> ElabError -> IO a
elabError cxt tgt err = throwIO $ ElabException $ ElabEx (_locals cxt) tgt err
{-# inline elabError #-}

unifySet :: Cxt -> P.Tm -> V.Val -> V.Val -> IO ()
unifySet cxt tgt a b =
  Unification.unifySet cxt a b `catch` \case
    CantUnify -> elabError cxt tgt $
                   UnifyError (quote cxt DontUnfold a) (quote cxt DontUnfold b)
    _         -> impossible

data Infer   = Infer S.Tm V.Ty S.U
data InferTy = InferTy S.Tm S.U

-- throwaway helper types for defining infer P.App
data InferApp1 = InferApp1 Icit S.Tm V.Ty S.U
data InferApp2 = InferApp2 V.Val S.U {-# unpack #-} V.Closure

freshTy :: Cxt -> IO InferTy
freshTy cxt = do
  u <- S.UVar <$> newUMeta
  a <- freshMeta cxt (V.WU u) S.Set
  pure $ InferTy a u
{-# inlinable freshTy #-}

inferTy :: Cxt -> P.Tm -> IO InferTy
inferTy cxt topA = do
  Infer a au _ <- infer cxt topA
  au <- case forceFU cxt au of
    V.U u -> pure u
    au    -> do
      u <- S.UVar <$> newUMeta
      unifySet cxt topA au (V.U u)
      pure u
  pure $ InferTy a au

-- | Insert fresh implicit applications.
insert' :: Cxt -> IO Infer -> IO Infer
insert' cxt inf = go cxt =<< inf where
  go cxt (Infer t topA topU) = case forceFUE cxt topA of
    V.Pi x Impl a au b -> do
      m <- freshMeta cxt (unS a) au
      go cxt (Infer (S.App t m au Impl) (b $$$ unS (eval cxt m)) topU)
    topA ->
      pure $ Infer t topA topU
{-# inline insert' #-}

-- | Insert fresh implicit applications to a neutral term.
insert :: Cxt -> IO Infer -> IO Infer
insert cxt inf = inf >>= \case
  res@(Infer (S.Lam _ Impl _ _ _) va _) -> pure res
  res                                   -> insert' cxt (pure res)
{-# inline insert #-}

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertUntilName :: Cxt -> P.Tm -> RawName -> IO Infer -> IO Infer
insertUntilName cxt tgt name act = go cxt tgt name =<< act where

  go :: Cxt -> P.Tm -> RawName -> Infer -> IO Infer
  go cxt tgt name (Infer t topA topU) = case forceFUE cxt topA of
    V.Pi x Impl a au b -> do
      if NName name == x then
        pure (Infer t topA topU)
      else do
        m <- freshMeta cxt (unS a) au
        go cxt tgt name (Infer (S.App t m au Impl) (b $$$ unS (eval cxt m)) topU)
    _ ->
      elabError cxt tgt $ NoSuchArgument name
{-# inline insertUntilName #-}


data Checking = Checking P.Tm V.Ty

check :: Cxt -> P.Tm -> V.Ty -> S.U -> IO S.Tm
check cxt t a au = S <$> wcheck cxt t a au; {-# inline check #-}
wcheck :: Cxt -> P.Tm -> V.Ty -> S.U -> IO S.WTm
wcheck cxt topmostT topA topU = case Checking topmostT (forceFUE cxt topA) of

  Checking (P.Lam _ x i t) (V.Pi x' i' a' au' b')
    | case i of NoName i                   -> i == i'
                Named (span2Name cxt -> x) -> x == x' -> do
    let qa' = quote cxt DontUnfold a'
    case x of
      P.Bind (span2RawName cxt -> x) ->
        S.WLam (NName x) i' qa' au' <$> check (bind' x qa' a' au' cxt) t (b' $$ V.Var (_lvl cxt)) topU
      P.DontBind ->
        S.WLam NEmpty i' qa' au' <$> check (bindEmpty' qa' a' au' cxt) t (b' $$ V.Var (_lvl cxt)) topU

  Checking t (V.Pi x' Impl a' au' b') -> do
    let qa' = quote cxt DontUnfold a'
    S.WLam x' Impl qa' au' <$> check (newBinder x' qa' au' cxt) t (b' $$ V.Var (_lvl cxt)) topU

  Checking (P.Pair t u) (V.Sg x a au b bu) -> do
    t <- check cxt t a au
    u <- check cxt u (b $$$ unS (eval cxt t)) bu
    pure $ S.WPair t au u bu

  Checking (P.Let _ (span2RawName cxt -> x) a t u) topA -> do
    InferTy a au <- maybe (freshTy cxt) (inferTy cxt) a
    let va = eval cxt a
    t <- check cxt t va au
    let ~vt = unS (eval cxt t)
    u <- check (define' x t vt a va au cxt) u topA topU
    pure $ S.WLet (NName x) a au t u

  Checking (P.Hole _) (topA) -> do
    wfreshMeta cxt (unS topA) topU

  Checking t topA -> do
    Infer t a au <- insert cxt $ infer cxt t
    unifySet cxt topmostT a topA
    pure (unS t)


maybeInferSet :: Cxt -> Maybe P.Tm -> IO S.Ty
maybeInferSet cxt a =
  maybe (freshTyInU cxt S.Set) (\a -> check cxt a V.Set S.Set) a
{-# inline maybeInferSet #-}

maybeCheckInSet :: Cxt -> Maybe P.Tm -> V.Ty -> IO S.Ty
maybeCheckInSet cxt t a =
  maybe (freshMeta cxt (unS a) S.Set) (\t -> check cxt t a S.Set) t
{-# inline maybeCheckInSet #-}


infer :: Cxt -> P.Tm -> IO Infer
infer cxt topmostT = case topmostT of

  P.Var (span2RawName cxt -> x) -> do
    case HM.lookup x (_nameTable cxt) of
      Just ni -> case ni of
        NITopDef    x a au -> pure $ Infer (S.TopDef x) a au
        NIPostulate x a au -> pure $ Infer (S.Postulate x) a au
        NILocal     x a au -> pure $ Infer (S.LocalVar (lvlToIx (_lvl cxt) x)) a au
      Nothing ->
        elabError cxt topmostT $ NameNotInScope x

  P.Let _ (span2RawName cxt -> x) a t u -> do
    InferTy a au <- maybe (freshTy cxt) (inferTy cxt) a
    let va = eval cxt a
    t <- check cxt t va au
    let ~vt = unS (eval cxt t)
    Infer u b bu <- infer (define' x t vt a va au cxt) u
    pure $ Infer (S.Let (NName x) a au t u) b bu

  P.Pi _ P.DontBind i a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy (bindEmpty a au cxt) b
    pure $ Infer (S.Pi NEmpty i a au b) (V.U bu) S.Set

  P.Pi _ (P.Bind (span2RawName cxt -> x)) i a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy (bind x a au cxt) b
    pure $ Infer (S.Pi (NName x) i a au b) (V.U bu) S.Set

  P.App rawT u inf -> do

    -- data InferApp1 = InferApp1 Icit S.Tm V.Ty S.U
    InferApp1 i t tty tu <- case inf of
      Named (span2RawName cxt -> x) -> do
        Infer t tty tu <- insertUntilName cxt topmostT x $ infer cxt rawT
        pure $ InferApp1 Impl t tty tu
      NoName Impl -> do
        Infer t tty tu <- infer cxt rawT
        pure $ InferApp1 Impl t tty tu
      NoName Expl -> do
        Infer t tty tu <- insert' cxt $ infer cxt rawT
        pure $ InferApp1 Expl t tty tu

    -- data InferApp2 = InferApp2 V.Val S.U {-# unpack #-} V.Closure
    InferApp2 a au b <- case forceFUE cxt tty of
      V.Pi x i' a au b -> do
        unless (i == i') $
          elabError cxt topmostT $ IcitMismatch i i'
        pure $ InferApp2 a au b
      topA -> do
        InferTy a au <- freshTy cxt
        InferTy b bu <- freshTy (bindEmpty a au cxt)
        let va = eval cxt a
        let vb = closeVal cxt (eval (bindEmpty a au cxt) b)
        unifySet cxt rawT topA (V.Pi NEmpty i va au vb)
        pure $ InferApp2 va au vb

    u <- check cxt u a au
    pure $ Infer (S.App t u au i) (b $$$ unS (eval cxt u)) tu

  P.Lam _ P.DontBind i t -> do
    i <- case i of NoName i -> pure i
                   _        -> elabError cxt topmostT $ NoNamedLambdaInference
    InferTy a au <- freshTy cxt
    let va = eval cxt a
    Infer t b bu <- infer (bindEmpty a au cxt) t
    pure $ Infer (S.Lam NEmpty i a au t) (V.Pi NEmpty i va au (closeVal cxt b)) bu

  P.Lam _ (P.Bind (span2RawName cxt -> x)) i t -> do
    i <- case i of NoName i -> pure i
                   _        -> elabError cxt topmostT $ NoNamedLambdaInference
    InferTy a au <- freshTy cxt
    let va = eval cxt a
    Infer t b bu <- infer (bind' x a va au cxt) t
    pure $ Infer (S.Lam (NName x) i a au t) (V.Pi (NName x) i va au (closeVal cxt b)) bu

  P.Sg _ P.DontBind a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy (bindEmpty a au cxt) b
    pure $ Infer (S.Sg NEmpty a au b bu) (V.U (au <> bu)) S.Set

  P.Sg _ (P.Bind (span2RawName cxt -> x)) a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy (bind x a au cxt) b
    pure $ Infer (S.Sg (NName x) a au b bu) (V.U (au <> bu)) S.Set

  P.Pair t u -> do               -- we only try to infer non-dependent Sg
    Infer t a au <- infer cxt t
    Infer u b bu <- infer cxt u
    pure $ Infer (S.Pair t au u bu) (V.prod a au b bu) (au <> bu)

  P.Proj1 t _ -> do
    Infer t topA topU <- infer cxt t
    case forceFUE cxt topA of
      V.Sg x a au b bu               -> pure $ Infer (S.Proj1 t) a au
      (quote cxt DontUnfold -> topA) -> elabError cxt topmostT $ ExpectedSg topA

  P.Proj2 t _ -> do
    Infer t topA topU <- infer cxt t
    case forceFUE cxt topA of
      V.Sg x a au b bu               -> pure $ Infer (S.Proj2 t) (b $$$ unS (vProj1 (eval cxt t))) bu
      (quote cxt DontUnfold -> topA) -> elabError cxt topmostT $ ExpectedSg topA

  P.ProjField t (span2RawName cxt -> topX) -> do
    Infer topT topA topU <- infer cxt t
    let go :: S.Tm -> V.Val -> V.Ty -> Int -> IO Infer
        go topT t sg i = case forceFUE cxt sg of
          V.Sg x a au b bu
            | NName topX == x -> pure $ Infer (S.ProjField topT x i) a au
            | otherwise       -> go topT (vProj2 t) (b $$$ unS (vProj2 t)) (i + 1)
          _ -> elabError cxt topmostT $ NoSuchField topX
    go topT (eval cxt topT) topA 0

  P.Set _  -> pure $ Infer (S.U S.Set)  V.Set S.Set
  P.Prop _ -> pure $ Infer (S.U S.Prop) V.Set S.Set
  P.Top _  -> pure $ Infer S.Top V.Prop S.Set
  P.Tt _   -> pure $ Infer S.Tt V.Top S.Prop
  P.Bot _  -> pure $ Infer S.Bot V.Prop S.Set

  P.Exfalso _ a p -> do
    u <- S.UVar <$> newUMeta
    a <- maybe (freshTyInU cxt u) (\a -> check cxt a (V.U u) S.Set) a
    p <- check cxt p V.Bot S.Prop
    pure $ Infer (S.Exfalso u a p) (eval cxt a) u

  P.Eq t u -> do
    Infer t a au <- infer cxt t
    let qa = quote cxt DontUnfold a
    u <- check cxt u a au
    pure $ Infer (S.Eq qa t u) V.Prop S.Set

  P.Refl _ a t -> do
    a <- maybeInferSet cxt a
    let va = eval cxt a
    t <- maybeCheckInSet cxt t va
    let ~vt = eval cxt t
    pure $ Infer (S.Refl a t) (vEq cxt va vt vt) S.Set

  P.Coe _ Nothing Nothing p t -> do
    Infer t a au <- infer cxt t
    b <- freshTyInU cxt S.Set
    let bv = eval cxt b
    p <- check cxt p (vEq cxt V.Set a bv) S.Set
    pure $ Infer (S.Coe (quote cxt DontUnfold a) b p t) bv S.Set

  P.Coe _ a b p t -> do
    a <- maybeInferSet cxt a
    let va = eval cxt a
    b <- maybeInferSet cxt b
    let vb = eval cxt b
    p <- check cxt p (vEq cxt V.Set va vb) S.Prop
    t <- check cxt t va S.Set
    pure $ Infer (S.Coe a b p t) vb S.Set

  P.Sym _ a x y p -> do
    a <- maybeInferSet cxt a
    let va = eval cxt a
    x <- maybeCheckInSet cxt x va
    let vx = eval cxt x
    y <- maybeCheckInSet cxt y va
    let vy = eval cxt y
    p <- check cxt p (vEq cxt va vx vy) S.Prop
    pure $ Infer (S.Sym a x y p) (vEq cxt va vy vx) S.Prop

  P.Trans _ a x y z p q -> do
    a <- maybeInferSet cxt a
    let va = eval cxt a
    x <- maybeCheckInSet cxt x va
    let vx = eval cxt x
    y <- maybeCheckInSet cxt y va
    let vy = eval cxt y
    z <- maybeCheckInSet cxt z va
    let vz = eval cxt z
    p <- check cxt p (vEq cxt va vx vy) S.Prop
    q <- check cxt q (vEq cxt va vy vz) S.Prop
    pure $ Infer (S.Trans a x y z p q) (vEq cxt va vx vz) S.Prop

  P.Ap _ a b f x y p -> do
    a <- maybeInferSet cxt a
    let va = eval cxt a
    b <- maybeInferSet cxt b
    let vb = eval cxt b
    f <- check cxt f (V.fun va S.Set vb) S.Set
    let vf = eval cxt f
    x <- maybeCheckInSet cxt x va
    let vx = eval cxt x
    y <- maybeCheckInSet cxt y va
    let vy = eval cxt y
    p <- check cxt p (vEq cxt va vx vy) S.Prop
    pure $ Infer (S.Ap a b f x y p) (vEq cxt va (vAppSE vf vx) (vAppSE vf vy)) S.Prop

  P.Hole _ -> do
    InferTy a au <- freshTy cxt
    t <- freshMeta' cxt a au
    pure $ Infer t (eval cxt a) au

--------------------------------------------------------------------------------

inspectS 'infer
