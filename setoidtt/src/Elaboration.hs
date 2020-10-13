{-# options_ghc -Wno-unused-imports #-}

module Elaboration where

import qualified Data.ByteString     as B
import qualified Data.HashMap.Strict as HM
import qualified Syntax              as S
import qualified Value               as V
import qualified Presyntax           as P
import qualified FlatParse           as FP

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

span2BS :: Cxt -> Span -> RawName
span2BS cxt span = RawName (FP.unsafeSpan2ByteString (unRawName (_src cxt)) span)

freshTy :: Cxt -> IO InferTy
freshTy cxt = do
  u <- S.UVar <$> newUMeta
  a <- freshMeta cxt (V.U u) S.Set
  pure $ InferTy a u

freshMeta :: Cxt -> V.Ty -> S.U -> IO S.Tm
freshMeta cxt a au = S <$> wfreshMeta cxt a au; {-# inline freshMeta #-}
wfreshMeta cxt a au = undefined

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
      m <- freshMeta cxt a au
      go cxt (Infer (S.App t m au Impl) (unS (b $$ eval cxt m)) topU)
    topA ->
      pure $ Infer t (unS topA) topU

-- | Insert fresh implicit applications to a neutral term.
insert :: Cxt -> IO Infer -> IO Infer
insert cxt inf = inf >>= \case
  res@(Infer (S.Lam _ Impl _ _ _) va _) -> pure res
  res                                   -> insert' cxt (pure res)

check :: Cxt -> P.Tm -> V.Ty -> S.U -> IO S.Tm
check cxt t a au = S <$> wcheck cxt t a au
wcheck :: Cxt -> P.Tm -> V.Ty -> S.U -> IO S.WTm
wcheck cxt topT (force cxt -> topA) topU = case (topT, topA) of
  (topT, V.Eq _ _ _ v) -> wcheck cxt topT (S v) topU

infer :: Cxt -> P.Tm -> IO Infer
infer cxt topT = case topT of

  P.Var rawx -> do
    let x = span2BS cxt rawx
    case HM.lookup x (_nameTable cxt) of
      Just ni -> case ni of
        NITopDef    x a au -> pure $ Infer (S.TopDef x) a au
        NIPostulate x a au -> pure $ Infer (S.Postulate x) a au
        NILocal     x a au -> pure $ Infer (S.LocalVar (lvlToIx (_lvl cxt) x)) a au
      Nothing ->
        error "name not in scope"

  P.Let _ (span2BS cxt -> x) a t u -> do
    InferTy a au <- maybe (freshTy cxt) (inferTy cxt) a
    let va = eval cxt a
    t <- check cxt t va au
    Infer u b bu <- infer (define' x t a va au cxt) u
    pure $ Infer (S.Let (NName x) a au t u) b bu

  P.Pi _ P.DontBind i a b -> do
    InferTy a au <- inferTy cxt a
    InferTy b bu <- inferTy cxt b
    pure $ Infer (S.Pi NEmpty i a au b) (V.WU bu) S.Set

  P.Pi _ (P.Bind (span2BS cxt -> x)) i a b -> do
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

  P.Hole _ -> do
    InferTy a au <- freshTy cxt
    let av = eval cxt a
    t <- freshMeta cxt av au
    pure $ Infer t (unS av) au

  _ -> undefined
