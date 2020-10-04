
module Value where

import Common
import Syntax (U(..), Tm, pattern Prop, type UMax)

--------------------------------------------------------------------------------

data Closure = Closure (# Val -> Val | (# Env, Tm #) #)

pattern CFun f       = Closure (# f | #)
pattern CClose env t = Closure (# | (# env, t #) #)
{-# complete CFun, CClose #-}

data Env = ENil | EDef Env ~Val

data RigidHead
  = RHBoundVar Lvl
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

  | SProj1 Spine U
  | SProj2 Spine U
  | SProjField Spine Name Int U

  | SCoeSrc Spine ~Val ~Val ~Val
  | SCoeTgt Val Spine ~Val ~Val
  | SCoeComp Val Val ~Val Spine

  | SEqType Spine ~Val ~Val
  | SEqSetLhs Spine ~Val
  | SEqSetRhs Val Spine

type VTy = Val
data Val
  -- Rigid stuck values
  = Rigid RigidHead Spine

  -- Flexibly stuck values
  | Flex FlexHead Spine

  | Unfold UnfoldHead Spine ~Val -- Non-deterministic unfoldings
  | Eq Val Val Val ~Val          -- An equality type which computes to a non-Eq type

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
vAnd a b = Sg "_" a Prop (CFun (\ ~_ -> b)) Prop
{-# inline vAnd #-}

vImpl :: Val -> Val -> Val
vImpl a b = PiEP "_" a (\ ~_ -> b)
{-# inline vImpl #-}
