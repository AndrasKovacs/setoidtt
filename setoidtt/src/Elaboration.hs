{-# options_ghc -Wno-unused-imports #-}

module Elaboration where

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
{-# inline wfreshMeta #-}

freshMeta' :: Cxt -> S.Ty -> S.U -> IO S.Tm
freshMeta' cxt a au = S <$> wfreshMeta' cxt a au; {-# inline freshMeta' #-}
wfreshMeta' :: Cxt -> S.Ty -> S.U -> IO S.WTm
wfreshMeta' cxt a au = do
  let ~va = unS (Eval.eval V.Nil 0 (closeType (_locals cxt) a))
  m <- newMeta va au
  pure $ S.WInsertedMeta m (_locals cxt)
{-# inline wfreshMeta' #-}

data Infer   = Infer S.Tm ~V.WTy S.U
data InferTy = InferTy S.Tm S.U

unifySet :: Cxt -> V.Val -> V.Val -> IO ()
unifySet cxt a a' = undefined

inferTy :: Cxt -> P.Tm -> IO InferTy
inferTy cxt a = do
  Infer a au _ <- infer cxt a
  au <- case force cxt (S au) of
    V.U u -> pure u
    au    -> do
      u <- S.UVar <$> newUMeta
      unifySet cxt au (V.U u)
      pure u
  pure $ InferTy a au

-- | Insert fresh implicit applications.
insert' :: Cxt -> IO Infer -> IO Infer
insert' cxt inf = go cxt =<< inf where
  go cxt (Infer t topA topU) = case force cxt (S topA) of
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
wcheck cxt topT topA topU = case Checking topT (force cxt topA) of

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
    let ~vt = eval cxt t
    Infer u b bu <- infer (define' x t vt a va au cxt) u
    pure $ Infer (S.Let (NName x) a au t u) b bu

  P.Pi _ P.DontBind i a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy cxt b
    pure $ Infer (S.Pi NEmpty i a au b) (V.WU bu) S.Set

  P.Pi _ (P.Bind (span2RawName cxt -> x)) i a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy (bind x a au cxt) b
    pure $ Infer (S.Pi (NName x) i a au b) (V.WU bu) S.Set

  P.App t u inf -> undefined
  P.Lam _ x i t -> undefined

  P.Sg _ x a b -> undefined
  P.Pair t u -> undefined
  P.Proj1 t _ -> undefined
  P.Proj2 t _ -> undefined
  P.ProjField t x -> undefined

  P.Set _  -> pure $ Infer (S.U S.Set)  V.WSet S.Set
  P.Prop _ -> pure $ Infer (S.U S.Prop) V.WSet S.Set
  P.Top _  -> pure $ Infer S.Top V.WProp S.Set
  P.Tt _   -> pure $ Infer S.Tt V.WTop S.Prop
  P.Bot _  -> pure $ Infer S.Bot V.WProp S.Set

  -- TODO : parse only fully applied builtins!
  -- P.Exfalso _ -> undefined
  -- P.Eq _ _    -> undefined
  -- P.Refl _    -> undefined
  -- P.Coe _     -> undefined
  -- P.Sym _     -> undefined
  -- P.Trans _   -> undefined
  -- P.Ap _      -> undefined

  P.Hole _ -> do
    InferTy a au <- freshTy cxt
    let va = unS (eval cxt a)
    t <- freshMeta' cxt a au
    pure $ Infer t va au


--------------------------------------------------------------------------------

inspectS 'infer
