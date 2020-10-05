
module Value where

import GHC.Types (Int(..))
import GHC.Prim (Int#)
import Common
import Syntax (U(..), Tm, pattern Prop, type UMax)

--------------------------------------------------------------------------------

-- TODO: optimize layout using direct unboxed tuples.
data Closure = Closure (# Val -> Val | (# Env, Int#, Tm #) #)

pattern CFun f = Closure (# f | #)

pattern CClose env l t <- Closure (# | (# env, (\x -> Lvl (I# x)) -> l, t #) #) where
  CClose env (Lvl (I# l)) t = Closure (# | (# env, l, t #) #)
{-# complete CFun, CClose #-}

data Env = ENil | EDef Env ~Val

data RigidHead
  = RHLocalVar Lvl
  | RHPostulate Lvl
  | RHRefl
  | RHSym
  | RHAp
  | RHTrans
  | RHExfalso U
  | RHCoe Val Val ~Val Val

data FlexHead
  -- blocking on Meta
  = FHMeta Meta
  | FHCoeRefl Meta Val Val Val Val

  -- blocking on UMax
  | FHCoeUMax UMax Val Val ~Val ~Val
  | FHEqUMax UMax Val Val Val

data UnfoldHead
  = UHMeta Meta
  | UHTopDef Lvl

-- Blocking on Val in nested ways.
data Spine
  = SNil
  | SApp Spine ~Val U Icit

  | SProj1 Spine
  | SProj2 Spine
  | SProjField Spine Name Int

  | SCoeSrc Spine ~Val ~Val ~Val  -- netural source type
  | SCoeTgt Val Spine ~Val ~Val   -- neutral target type
  | SCoeComp Val Val ~Val Spine   -- composition blocking on neutral coerced value

  | SEqType Spine ~Val ~Val
  | SEqSetLhs Spine ~Val
  | SEqSetRhs Val Spine

type VTy = Val
data Val
  -- Rigidly stuck values
  = Rigid RigidHead Spine

  -- Flexibly stuck values
  | Flex FlexHead Spine

  -- Non-deterministic values
  | Unfold UnfoldHead Spine ~Val -- unfolding choice (top/meta)
  | Eq Val Val Val ~Val          -- Eq computation to non-Eq type

  -- Canonical values
  | U U
  | Top
  | Tt
  | Bot
  | Pair ~Val U ~Val U
  | Sg  Name       VTy U {-# unpack #-} Closure U
  | Pi  Name Icit ~VTy U {-# unpack #-} Closure
  | Lam Name Icit ~VTy U {-# unpack #-} Closure

--------------------------------------------------------------------------------

pattern VVar x = Rigid (RHLocalVar x) SNil

pattern SAppIS sp t = SApp sp t Set  Impl
pattern SAppES sp t = SApp sp t Set  Expl
pattern SAppIP sp t = SApp sp t Prop Impl
pattern SAppEP sp t = SApp sp t Prop Expl

pattern LamIS x a b = Lam x Impl a Set  (CFun b)
pattern LamES x a b = Lam x Expl a Set  (CFun b)
pattern LamIP x a b = Lam x Impl a Prop (CFun b)
pattern LamEP x a b = Lam x Expl a Prop (CFun b)

pattern PiES x a b = Pi x Expl a Set  (CFun b)
pattern PiEP x a b = Pi x Expl a Prop (CFun b)
pattern SgPP x a b = Sg x a Prop (CFun b) Prop

pattern VMeta m      = Flex (FHMeta m) SNil
pattern VSet         = U Set
pattern VProp        = U Prop
pattern VRefl a t    = Rigid RHRefl (SNil `SAppIS` a `SAppES` t)
pattern VSym a x y p = Rigid RHSym (SNil `SAppIS` a `SAppIS` x `SAppIS` y `SAppES` p)

pattern VTrans a x y z p q =
  Rigid RHTrans (SNil `SAppIS` a `SAppIS` x `SAppIS` y `SAppIS` z `SAppEP` p `SAppEP` q)

pattern VAp a b f x y p =
  Rigid RHAp (SNil `SAppIS` a `SAppIS` b `SAppES` f `SAppIS` x `SAppIS` y `SAppEP` p)

pattern VExfalso u a p =
  Rigid (RHExfalso u) (SNil `SAppIS` a `SAppEP` p)

vAnd :: Val -> Val -> Val
vAnd ~a ~b = Sg "_" a Prop (CFun (\ ~_ -> b)) Prop
{-# inline vAnd #-}

vImpl :: Val -> Val -> Val
vImpl ~a ~b = PiEP "_" a (\ ~_ -> b)
{-# inline vImpl #-}
