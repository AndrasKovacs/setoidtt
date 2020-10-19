{-# options_ghc -Wno-unused-imports #-}

module Elaboration (infer, check, bind2Name, insert, insert') where

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
import EvalCxt
import Unification

{- CORE INSPECTION
- try to prevent unpacking the ByteString in Cxt
- HashMap adds a bit of noise
-}

--------------------------------------------------------------------------------

span2RawName :: Cxt -> Span -> RawName
span2RawName cxt span = RawName (FP.unsafeSpan2ByteString (unRawName (_src cxt)) span)

span2Name :: Cxt -> Span -> Name
span2Name cxt = NName . span2RawName cxt

bind2Name :: Cxt -> P.Bind -> Name
bind2Name cxt (P.Bind x) = NName (span2RawName cxt x)
bind2Name cxt P.DontBind = NEmpty

--------------------------------------------------------------------------------

freshTyInU :: Cxt -> S.U -> IO S.Ty
freshTyInU cxt u = S <$> wfreshTyInU cxt u; {-# inline freshTyInU #-};
wfreshTyInU :: Cxt -> S.U -> IO S.WTy
wfreshTyInU cxt u = wfreshMeta cxt (V.WU u) S.Set

freshTy :: Cxt -> IO InferTy
freshTy cxt = do
  u <- S.UVar <$> newUMeta
  a <- freshMeta cxt (V.WU u) S.Set
  pure $ InferTy a u

closeType :: S.Locals -> S.Ty -> S.Ty
closeType ls topA = case ls of
  S.Empty              -> topA
  S.Define ls x t a au -> closeType ls (S.Let x a au t topA)
  S.Bind ls x a au     -> closeType ls (S.Pi x Expl a au topA)

freshMeta :: Cxt -> V.WTy -> S.U -> IO S.Tm
freshMeta cxt ~va au = S <$> wfreshMeta cxt va au; {-# inline freshMeta #-}
wfreshMeta :: Cxt -> V.WTy -> S.U -> IO S.WTm
wfreshMeta cxt ~va au = do
  wfreshMeta' cxt (quote cxt DontUnfold (S va)) au

freshMeta' :: Cxt -> S.Ty -> S.U -> IO S.Tm
freshMeta' cxt a au = S <$> wfreshMeta' cxt a au; {-# inline freshMeta' #-}
wfreshMeta' :: Cxt -> S.Ty -> S.U -> IO S.WTm
wfreshMeta' cxt a au = do
  let ~va = unS (Eval.eval V.Nil 0 (closeType (_locals cxt) a))
  m <- newMeta va au
  pure $ S.WInsertedMeta m (_locals cxt)

--------------------------------------------------------------------------------

data Infer   = Infer S.Tm ~V.WTy S.U
data InferTy = InferTy S.Tm S.U


inferTy :: Cxt -> P.Tm -> IO InferTy
inferTy cxt a = do
  Infer a au _ <- infer cxt a
  au <- case forceFU cxt (S au) of
    V.U u -> pure u
    au    -> do
      u <- S.UVar <$> newUMeta
      unifySet cxt au (V.U u)
      pure u
  pure $ InferTy a au

-- | Insert fresh implicit applications.
insert' :: Cxt -> IO Infer -> IO Infer
insert' cxt inf = go cxt =<< inf where
  go cxt (Infer t topA topU) = case forceFUE cxt (S topA) of
    V.Pi x Impl a au b -> do
      m <- freshMeta cxt (unS a) au
      go cxt (Infer (S.App t m au Impl) (unS (b $$ eval cxt m)) topU)
    topA ->
      pure $ Infer t (unS topA) topU

-- | Insert fresh implicit applications to a neutral term.
insert :: Cxt -> IO Infer -> IO Infer
insert cxt inf = inf >>= \case
  res@(Infer (S.Lam _ Impl _ _ _) va _) -> pure res
  res                                   -> insert' cxt (pure res)

data Checking = Checking P.Tm V.Ty

check :: Cxt -> P.Tm -> V.Ty -> S.U -> IO S.Tm
check cxt t a au = S <$> wcheck cxt t a au; {-# inline check #-}
wcheck :: Cxt -> P.Tm -> V.Ty -> S.U -> IO S.WTm
wcheck cxt topT topA topU = case Checking topT (forceFUE cxt topA) of
  Checking topT (V.Eq _ _ _ v) -> do
    wcheck cxt topT v topU

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
    let ~vt = eval cxt t
    u <- check (define' x t vt a va au cxt) u topA topU
    pure $ S.WLet (NName x) a au t u

  Checking (P.Hole _) (topA) -> do
    wfreshMeta cxt (unS topA) topU

  Checking t topA -> do
    Infer t a au <- infer cxt t
    undefined

maybeInferSet :: Cxt -> Maybe P.Tm -> IO S.Ty
maybeInferSet cxt a =
  maybe (freshTyInU cxt S.Set) (\a -> check cxt a V.Set S.Set) a
{-# inline maybeInferSet #-}

maybeCheckInSet :: Cxt -> Maybe P.Tm -> V.Ty -> IO S.Ty
maybeCheckInSet cxt t a =
  maybe (freshMeta cxt (unS a) S.Set) (\t -> check cxt t a S.Set) t
{-# inline maybeCheckInSet #-}

infer :: Cxt -> P.Tm -> IO Infer
infer cxt topT = case topT of

  P.Var (span2RawName cxt -> x) -> do
    case HM.lookup x (_nameTable cxt) of
      Just ni -> case ni of
        NITopDef    x a au -> pure $ Infer (S.TopDef x) a au
        NIPostulate x a au -> pure $ Infer (S.Postulate x) a au
        NILocal     x a au -> pure $ Infer (S.LocalVar (lvlToIx (_lvl cxt) x)) a au
      Nothing ->
        error "name not in scope"

  P.Let _ (span2RawName cxt -> x) a t u -> do
    InferTy a au <- maybe (freshTy cxt) (inferTy cxt) a
    let va = eval cxt a
    t <- check cxt t va au
    let ~vt = unS (eval cxt t)
    Infer u b bu <- infer (define' x t (S vt) a va au cxt) u
    pure $ Infer (S.Let (NName x) a au t u) b bu

  P.Pi _ P.DontBind i a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy (bindEmpty a au cxt) b
    pure $ Infer (S.Pi NEmpty i a au b) (V.WU bu) S.Set

  P.Pi _ (P.Bind (span2RawName cxt -> x)) i a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy (bind x a au cxt) b
    pure $ Infer (S.Pi (NName x) i a au b) (V.WU bu) S.Set

  P.App t u inf -> undefined

  P.Lam _ P.DontBind i t -> do
    i <- case i of NoName i -> pure i; _ -> undefined
    InferTy a au <- freshTy cxt
    let va = eval cxt a
    Infer t b bu <- infer (bindEmpty a au cxt) t
    pure $ Infer (S.Lam NEmpty i a au t) (V.WPi NEmpty i va au (closeVal cxt (S b))) bu

  P.Lam _ (P.Bind (span2RawName cxt -> x)) i t -> do
    i <- case i of NoName i -> pure i; _ -> undefined
    InferTy a au <- freshTy cxt
    let va = eval cxt a
    Infer t b bu <- infer (bind' x a va au cxt) t
    pure $ Infer (S.Lam (NName x) i a au t) (V.WPi (NName x) i va au (closeVal cxt (S b))) bu

  P.Sg _ P.DontBind a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy (bindEmpty a au cxt) b
    pure $ Infer (S.Sg NEmpty a au b bu) (V.WU (au <> bu)) S.Set

  P.Sg _ (P.Bind (span2RawName cxt -> x)) a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy (bind x a au cxt) b
    pure $ Infer (S.Sg (NName x) a au b bu) (V.WU (au <> bu)) S.Set

  P.Pair t u -> do               -- we only try to infer non-dependent Sg
    Infer t a au <- infer cxt t
    Infer u b bu <- infer cxt u
    pure $ Infer (S.Pair t au u bu) (V.wprod (S a) au (S b) bu) (au <> bu)

  P.Proj1 t _ -> do
    Infer t topA topU <- infer cxt t
    case forceFUE cxt (S topA) of
      V.Sg x a au b bu -> pure $ Infer (S.Proj1 t) (unS a) au
      topA             -> undefined

  P.Proj2 t _ -> do
    Infer t topA topU <- infer cxt t
    case forceFUE cxt (S topA) of
      V.Sg x a au b bu -> pure $ Infer (S.Proj2 t) (unS (vProj1 (eval cxt t))) bu
      topA             -> undefined

  P.ProjField t x ->
    undefined

  P.Set _  -> pure $ Infer (S.U S.Set)  V.WSet S.Set
  P.Prop _ -> pure $ Infer (S.U S.Prop) V.WSet S.Set
  P.Top _  -> pure $ Infer S.Top V.WProp S.Set
  P.Tt _   -> pure $ Infer S.Tt V.WTop S.Prop
  P.Bot _  -> pure $ Infer S.Bot V.WProp S.Set

  P.Exfalso _ a p -> do
    u <- S.UVar <$> newUMeta
    a <- maybe (freshTyInU cxt u) (\a -> check cxt a (V.U u) S.Set) a
    p <- check cxt p V.Bot S.Prop
    pure $ Infer (S.Exfalso u a p) (unS (eval cxt a)) u

  P.Eq t u -> do
    Infer t a au <- infer cxt t
    let qa = quote cxt DontUnfold (S a)
    u <- check cxt u (S a) au
    pure $ Infer (S.Eq qa t u) V.WProp S.Set

  P.Refl _ a t -> do
    a <- maybeInferSet cxt a
    let va = eval cxt a
    t <- maybeCheckInSet cxt t va
    let ~vt = eval cxt t
    pure $ Infer (S.Refl a t) (unS (vEq cxt va vt vt)) S.Set

  P.Coe _ Nothing Nothing p t -> do
    Infer t a au <- infer cxt t
    b <- freshTyInU cxt S.Set
    let bv = eval cxt b
    p <- check cxt p (vEq cxt V.Set (S a) bv) S.Set
    pure $ Infer (S.Coe (quote cxt DontUnfold (S a)) b p t) (unS bv) S.Set

  P.Coe _ a b p t -> do
    a <- maybeInferSet cxt a
    let va = eval cxt a
    b <- maybeInferSet cxt b
    let vb = eval cxt b
    p <- check cxt p (vEq cxt V.Set va vb) S.Prop
    t <- check cxt t va S.Set
    pure $ Infer (S.Coe a b p t) (unS vb) S.Set

  P.Sym _ a x y p -> do
    a <- maybeInferSet cxt a
    let va = eval cxt a
    x <- maybeCheckInSet cxt x va
    let vx = eval cxt x
    y <- maybeCheckInSet cxt y va
    let vy = eval cxt y
    p <- check cxt p (vEq cxt va vx vy) S.Prop
    pure $ Infer (S.Sym a x y p) (unS (vEq cxt va vy vx)) S.Prop

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
    pure $ Infer (S.Trans a x y z p q) (unS (vEq cxt va vx vz)) S.Prop

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
    pure $ Infer (S.Ap a b f x y p) (unS (vEq cxt va (vAppSE vf vx) (vAppSE vf vy))) S.Prop

  P.Hole _ -> do
    InferTy a au <- freshTy cxt
    let va = unS (eval cxt a)
    t <- freshMeta' cxt a au
    pure $ Infer t va au


--------------------------------------------------------------------------------

inspectS 'infer
