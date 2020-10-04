
module Value where

import qualified Data.IntSet as IS
import Common
import Syntax (U(..), Tm, pattern Prop)

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
  | RHCoe Val Val ~Val Val        -- Rigidly stuck coercion.

data FlexHead
  -- blocking on Meta
  = FHMeta Meta

  -- All the different ways of blocking on UMax (rather horrible!)
  --------------------------------------------------------------------------------

  | FHCoePiUMax1 Name Icit ~VTy IS.IntSet {-# unpack #-} Closure
                 Name Icit ~VTy U         {-# unpack #-} Closure ~Val ~Val
  | FHCoePiUMax2 Name Icit ~VTy U         {-# unpack #-} Closure
                 Name Icit ~VTy IS.IntSet {-# unpack #-} Closure ~Val ~Val

  | FHEqCoeSgUMax11 Name ~VTy IS.IntSet {-# unpack #-} Closure U
                    Name ~VTy U         {-# unpack #-} Closure U         ~Val ~Val
  | FHEqCoeSgUMax12 Name ~VTy U         {-# unpack #-} Closure IS.IntSet
                    Name ~VTy U         {-# unpack #-} Closure U         ~Val ~Val
  | FHEqCoeSgUMax21 Name ~VTy U         {-# unpack #-} Closure U
                    Name ~VTy IS.IntSet {-# unpack #-} Closure U         ~Val ~Val
  | FHEqCoeSgUMax22 Name ~VTy U         {-# unpack #-} Closure U
                    Name ~VTy U         {-# unpack #-} Closure IS.IntSet ~Val ~Val

  | FHEqUMax IS.IntSet ~Val ~Val
  | FHEqSgUMax1 Name ~VTy IS.IntSet Closure U
  | FHEqSgUMax2 Name ~VTy U Closure IS.IntSet

  | FHEqSetUMax1 IS.IntSet U
  | FHEqSetUMax2 U IS.IntSet

  | FHEqSetPiUMax1 Name Icit ~VTy IS.IntSet {-# unpack #-} Closure
                   Name Icit ~VTy U         {-# unpack #-} Closure
  | FHEqSetPiUMax2 Name Icit ~VTy U         {-# unpack #-} Closure
                   Name Icit ~VTy IS.IntSet {-# unpack #-} Closure

  | FHEqSetSgUMax11 Name ~VTy IS.IntSet {-# unpack #-} Closure U
                    Name ~VTy U         {-# unpack #-} Closure U
  | FHEqSetSgUMax12 Name ~VTy U         {-# unpack #-} Closure IS.IntSet
                    Name ~VTy U         {-# unpack #-} Closure U
  | FHEqSetSgUMax21 Name ~VTy U         {-# unpack #-} Closure U
                    Name ~VTy IS.IntSet {-# unpack #-} Closure U
  | FHEqSetSgUMax22 Name ~VTy U         {-# unpack #-} Closure U
                    Name ~VTy U         {-# unpack #-} Closure IS.IntSet

data UnfoldHead
  = UHMeta Meta
  | UHTopDef Lvl

-- All the different ways of blocking on a Val in a nested way.
data Spine
  = SNil
  | SApp Spine ~Val U Icit

  | SProj1 Spine U
  | SProj2 Spine U
  | SProjField Spine Name Int U

  | SCoeSrc Spine ~Val ~Val ~Val
  | SCoeTgt Val Spine ~Val ~Val
  | SCoeComp Val Val ~Val Spine
  | SCoeRefl Val Val ~Val Val

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
