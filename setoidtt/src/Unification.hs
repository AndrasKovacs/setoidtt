
module Unification where

import Common
import Cxt
import ElabState
import EvalInCxt

import qualified Evaluation as E
import qualified Syntax as S
import qualified Values as V

--------------------------------------------------------------------------------

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
{-# inlinable wfreshMeta #-}

freshMeta' :: Cxt -> S.Ty -> S.U -> IO S.Tm
freshMeta' cxt a au = S <$> wfreshMeta' cxt a au; {-# inline freshMeta' #-}
wfreshMeta' :: Cxt -> S.Ty -> S.U -> IO S.WTm
wfreshMeta' cxt a au = do
  let va = E.eval V.Nil 0 (closeType (_locals cxt) a)
  m <- newMeta va au
  pure $ S.WInsertedMeta m (_locals cxt)
{-# inlinable wfreshMeta' #-}

freshTyInU :: Cxt -> S.U -> IO S.Ty
freshTyInU cxt u = S <$> wfreshTyInU cxt u; {-# inline freshTyInU #-};
wfreshTyInU :: Cxt -> S.U -> IO S.WTy
wfreshTyInU cxt u = wfreshMeta cxt (V.WU u) S.Set
{-# inlinable wfreshTyInU #-}

--------------------------------------------------------------------------------

unifySet :: Cxt -> V.Val -> V.Val -> IO ()
unifySet cxt a a' = undefined
