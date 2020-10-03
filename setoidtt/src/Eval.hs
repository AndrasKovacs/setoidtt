
module Eval where

import IO
import qualified Data.IntSet as IS

import Common
import ElabState
import Syntax (U(..), Tm, pattern Prop, pattern UVar)
import Value
import qualified Syntax as S


--------------------------------------------------------------------------------

vLocalVar :: Env -> Ix -> Val
vLocalVar (EDef _ v)   0 = v
vLocalVar (EDef env _) x = vLocalVar env (x - 1)
vLocalVar _ _            = impossible

vMeta :: Meta -> Val
vMeta x = case runIO (readMeta x) of
  MEUnsolved{} -> Flex (FHMeta x) SNil
  MESolved v   -> Unfold (UHMeta x) SNil v
{-# inline vMeta #-}

vTopDef :: Lvl -> Val
vTopDef x = case runIO (readTop x) of
  TEDef v _ _ _ _ -> Unfold (UHTopDef x) SNil v
  _               -> impossible
{-# inline vTopDef #-}

forceU :: U -> U
forceU = \case
  Set     -> Set
  Prop    -> Prop
  UMax as -> IS.foldl' go Prop as where
               go u x = u <> maybe (UVar (UMeta x)) forceU (runIO (readUMeta (UMeta x)))
               {-# inline go #-}

infixl 2 $$
($$) :: Closure -> Val -> Val
($$) cl ~u = case cl of
  CFun t       -> t u
  CClose env t -> eval (EDef env u) t
{-# inline ($$) #-}

vApp :: Val -> Val -> U -> Icit -> Val
vApp t ~u un i = case t of
  Lam _ _ _ _ t -> t $$ u
  Rigid h sp    -> Rigid  h (SApp sp u un i)
  Flex h sp     -> Flex   h (SApp sp u un i)
  Unfold h sp t -> Unfold h (SApp sp u un i) (vApp t u un i)
  _             -> impossible

vProj1 :: Val -> U -> Val
vProj1 t tu = case t of
  Pair t _ u _  -> t
  Rigid h sp    -> Rigid  h (SProj1 sp tu)
  Flex h sp     -> Flex   h (SProj1 sp tu)
  Unfold h sp t -> Unfold h (SProj1 sp tu) (vProj1 t tu)
  _             -> impossible

vProj2 :: Val -> U -> Val
vProj2 t tu = case t of
  Pair t _ u _  -> u
  Rigid h sp    -> Rigid  h (SProj2 sp tu)
  Flex h sp     -> Flex   h (SProj2 sp tu)
  Unfold h sp t -> Unfold h (SProj2 sp tu) (vProj2 t tu)
  _             -> impossible

vProjField :: Val -> Name -> Int -> U -> Val
vProjField t x n tu = case t of
  Pair t tu u uu -> case n of 0 -> t
                              n -> vProjField u x (n - 1) uu
  Rigid h sp     -> Rigid  h (SProjField sp x n tu)
  Flex h sp      -> Flex   h (SProjField sp x n tu)
  Unfold h sp t  -> Unfold h (SProjField sp x n tu) (vProjField t x n tu)
  _              -> impossible

-- | Try to compute canonical coercions.
vCoe :: Val -> Val -> Val -> Val -> Val
vCoe ~a ~b ~p ~t = case (a, b) of
  (Pi x i a au b, Pi x' i' a' au' b') -> undefined
  (Sg x a au b bu, Sg x' a' au' b' bu') -> undefined

  (Flex h sp    , b            ) -> Flex h (SCoeSrc sp b p t)
  (Unfold h sp a, b            ) -> Unfold h (SCoeSrc sp b p t) (vCoe a b p t)
  (a            , Flex h sp    ) -> Flex h (SCoeTgt a sp p t)
  (a            , Unfold h sp b) -> Unfold h (SCoeTgt a sp p t) (vCoe a b p t)
  (a            , b            ) -> vCoeComp a b p t

-- | Try to compute coercion composition.
vCoeComp :: Val -> Val -> Val -> Val -> Val
vCoeComp ~a ~b ~p t = case t of
  Flex h sp                     -> Flex h (SCoeComp a b p sp)
  Unfold h sp t                 -> Unfold h (SCoeComp a b p sp) (vCoeComp a b p t)
  Rigid (RHCoe a' _ p' t') SNil -> vCoeRefl a' b (VTrans VSet a' a b p' p) t'
  t                             -> vCoeRefl a b p t

-- | Try to compute reflexive coercion.
vCoeRefl :: Val -> Val -> Val -> Val -> Val
vCoeRefl ~a ~b ~p ~t = undefined

vEq :: Val -> Val -> Val -> Val
vEq = undefined

vEqLhs :: Val -> Val -> Val -> Val
vEqLhs = undefined

vEqRhs :: Val -> Val -> Val -> Val
vEqRhs = undefined

vAppSp :: Val -> Spine -> Val
vAppSp ~v = go where
  go SNil                    = v
  go (SApp sp t tu i)        = vApp (go sp) t tu i

  go (SProj1 sp spu)         = vProj1 (go sp) spu
  go (SProj2 sp spu)         = vProj2 (go sp) spu
  go (SProjField sp x n spu) = vProjField (go sp) x n spu

  go (SCoeSrc a b p t)       = vCoe (go a) b p t
  go (SCoeTgt a b p t)       = vCoe a (go b) p t
  go (SCoeComp a b p t)      = vCoeComp a b p (go t)
  go (SCoeRefl a b p t)      = vCoeRefl a b p t

  go (SEqType a t u)         = vEq (go a) t u
  go (SEqLhs  a t u)         = vEqLhs a (go t) u
  go (SEqRhs  a t u)         = vEqLhs a t (go u)

eval :: Env -> Tm -> Val
eval ~env = go where
  go = \case
    S.LocalVar x         -> vLocalVar env x
    S.TopDef x           -> vTopDef x
    S.Postulate x        -> Rigid (RHPostulate x) SNil
    S.MetaVar x          -> vMeta x
    S.Let _ _ _ t u      -> eval (EDef env (go t)) u
    S.Pi x i a au b      -> Pi x i (go a) au (CClose env b)
    S.Sg x a au b bu     -> Sg x (go a) au (CClose env b) bu
    S.Lam x i a au t     -> Lam x i (go a) au (CClose env t)
    S.App t u uu i       -> vApp (go t) (go u) uu i
    S.Proj1 t tu         -> vProj1 (go t) tu
    S.Proj2 t tu         -> vProj2 (go t) tu
    S.ProjField t x n tu -> vProjField (go t) x n tu
    S.Pair t tu u uu     -> Pair (go t) tu (go u) uu
    S.U u                -> U u
    S.Top                -> Top
    S.Tt                 -> Tt
    S.Bot                -> Bot
    S.Eq                 -> LamIS "A" VSet \ ~a -> LamES "x" a \ ~x -> LamES "y" a \ ~y ->
                            vEq a x y
    S.Coe                -> LamIS "A" VSet \ ~a -> LamIS "B" VSet \ ~b ->
                            LamEP "p" (vEq VSet a b) \ ~p -> LamES "t" a \ ~t ->
                            vCoe a b p t
    S.Refl               -> LamIS "A" VSet \ ~a -> LamIS "x" a \ ~x -> VRefl a x
    S.Sym                -> LamIS "A" VSet \ ~a -> LamIS "x" a \ ~x ->
                            LamIS "y" a \ ~y -> LamEP "p" (vEq a x y) \ ~p ->
                            VSym a x y p
    S.Trans              -> LamIS "A" VSet \ ~a -> LamIS "x" a \ ~x ->
                            LamIS "y" a \ ~y -> LamIS "z" a \ ~z ->
                            LamEP "p" (vEq a x y) \ ~p -> LamEP "q" (vEq a y z) \ ~q ->
                            VTrans a x y z p q
    S.Ap                 -> LamIS "A" VSet \ ~a -> LamIS "B" VSet \ ~b ->
                            LamES "f" (PiES "_" a (const b)) \ ~f -> LamIS "x" a \ ~x ->
                            LamIS "y" a \ ~y -> LamEP "p" (vEq a x y) \ ~p ->
                            VAp a b f x y p
    S.Exfalso u          -> LamIS "A" (U u) \ ~a -> LamEP "p" Bot \ ~t -> VExfalso u a t



-- convert :: Lvl -> U -> Val -> Val -> ConvRes
