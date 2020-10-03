
module Value where

import Common
import Syntax (U(..), Tm, pattern Prop)

import qualified Data.IntSet as IS

{-

Principles:
- Computation can get stuck rigidly, in which case nothing can make it progress, or
  flexibly, which can be progressed by meta solutions.

- We clearly distinguish rigid and flex neutrals in the top Val type.
  Only flex neutrals every need to be forced.

- In unification problems, a problem can be potentially blocked on an arbitrary number
  of metas. But what about computation?
  + Elimination is only ever blocked on a single meta
  + Eq can be blocked on a flex type or when one side is flex neutral.
    If both sides are flex neutral, then Eq is blocked on 2 metas
  + Coe can block
     - on universe (1)
     - if the target or source type is flex neutral (max 2)
     - if the target/source are rigid neutral, then the composition rule can block
       on the coe body being flex neutra (1)
     - regularity can block on max 1 meta, bc it cannot progress after the first block

  Hence, Eq can block on 2 things, and coe can also block on 2 things at the same time.
  Can blocking things multiply? Yes, for example if Eq blocks on 2 coe expressions which also block
  on 2 things.

  Complication: although both Eq and coe can block on multiple things, it's possible that
  if 1 of many blocking metas is solved, that unblocks the whole computation! So even if we store
  many blocking metas, we if any of them is solved we have to re-force. Perhaps we can try to
  somehow be more clever, but I don't think it's worth it!

  Conclusion: we should remember exactly one blocking meta.
-}

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
  = FHMeta Meta
  | FHUMeta IS.IntSet

data UnfoldHead
  = UHMeta Meta
  | UHTopDef Lvl

data Spine
  = SNil

  | SApp Spine ~Val U Icit

  -- blocked projections
  | SProj1 Spine U
  | SProj2 Spine U
  | SProjField Spine Name Int U

  -- blocked coercions. We split of the full rigid stuck coe into RigidHead, because
  -- that's not blocked on any single head symbol; rather it's blocked because of the
  -- rigid failure of regularity check.
  | SCoeSrc Spine ~Val ~Val ~Val  -- stuck on flex source type
  | SCoeTgt Val Spine ~Val ~Val   -- stuck on flex target type
  | SCoeComp Val Val ~Val Spine   -- tgt & src both rigid neutral but body is flex
  | SCoeRefl Val Val ~Val Val     -- stuck on meta in regularity check (no recursive Spine!)

  -- blocked Eq type
  | SEqType Spine ~Val ~Val
  | SEqLhs VTy Spine ~Val
  | SEqRhs VTy Val Spine

type VTy = Val
data Val
  -- Rigid stuck values
  = Rigid RigidHead Spine

  -- Flexibly stuck values
  | Flex FlexHead Spine

  -- Non-deterministic unfoldings
  | Unfold UnfoldHead Spine ~Val
  | Eq Val Val ~Val  -- An equality type which computes to a non-Eq type

  -- Canonical values
  | U U
  | Top
  | Tt
  | Bot
  | Pair ~Val U ~Val U
  | Sg  Name       VTy U {-# unpack #-} Closure U
  | Pi  Name Icit ~VTy U {-# unpack #-} Closure
  | Lam Name Icit ~VTy U {-# unpack #-} Closure

pattern SAppIS sp t = SApp sp t Set  Impl
pattern SAppES sp t = SApp sp t Set  Expl
pattern SAppIP sp t = SApp sp t Prop Impl
pattern SAppEP sp t = SApp sp t Prop Expl

pattern LamIS x a b = Lam x Impl a Set  (CFun b)
pattern LamES x a b = Lam x Expl a Set  (CFun b)
pattern LamIP x a b = Lam x Impl a Prop (CFun b)
pattern LamEP x a b = Lam x Expl a Prop (CFun b)

pattern PiES x a b = Pi x Expl a Set (CFun b)

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
