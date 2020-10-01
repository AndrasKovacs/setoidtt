
module Value where

import Common
import qualified Syntax as S


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

data Closure


-- | Builtin constants which be eliminated (applied, projected), but the eliminations
--   can never progress.
data Axiom
  = ARefl
  | ASym
  | ATrans
  | AExfalso U

-- | Expressions which be eliminated (applied, projected), but the eliminations
--   can never progress.
data RigidHead
  = RHLocalVar Lvl
  | RHPostulate Lvl
  | RHAxiom Axiom
  | RHCoe Val Val ~Val Val  -- ^ Rigid coercion. We don't know here exactly what blocked
                            --   coe, but we don't care bc this coe can't ever be forced.

data Spine
  = SNil
  | SApp Spine

data FlexHead
  = FHMeta Meta
  | FHCoe Meta Val Val ~Val Val

type VTy = Val

data Val
  = NeRigid RigidHead Spine   -- ^ Elimination which cannot progress.
  | NeFlex FlexHead Spine     -- ^ Elimination which might progress.

  | EqRigid Val Val Val       -- ^ Equality type which cannot compute.
  | EqFlex Meta Val Val Val   -- ^ Equality type which might compute.

  | UnfoldTop Lvl Spine ~Val  -- ^ Lazy non-deterministic unfolding of a top-level definition.
  | UnfoldEq Val Val Val Val  -- ^ Trace of an Eq computation which reduces to a non-Eq type.
                              --   "UnfoldEq a t u b" implies that (b = Eq a t u) and
                              --   b is a canonical type different to Eq.

  | Top
  | Tt
  | Bot
  | Pair ~Val U ~Val U
  | Sg Name VTy U {-# unpack #-} Closure U
  | Pi Name Icit ~VTy U {-# unpack #-} Closure
  | Lam Name Icit ~VTy U {-# unpack #-} Closure





-- data Head
--   = HLocalVar Lvl
--   | HTopVar Lvl
--   | HMeta Meta
--   | HAxiom Axiom
--   | HCoe U Val Val ~Val Val

-- data Head
--   = HVar Lvl
--   | HMeta MId
--   | HAxiom Axiom
--   | HCoe U Val Val ~Val Val

-- data Val
--   = VNe Head Spine
--   | VPi Name Icit ~VTy U (VTy -> VTy)
--   | VLam Name Icit ~VTy U (Val -> Val)
--   | VU U
--   | VTop
--   | VTt
--   | VBot
--   | VEqGlue Val Val Val Val -- ^ (VGlue a t u b) means that b is a type which is definitionally
--                             --   Equal to (Eq a t u).
--                             --   Invariant: b is a canonical type *different* from Eq!
--   | VEq Val Val Val
--   | VSg Name ~Val U (VTy -> VTy) U
--   | VPair ~Val U ~Val U

--   | VNat
--   | VZero
--   | VSuc ~Val
