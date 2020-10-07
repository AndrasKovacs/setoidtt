
module Value where

import GHC.Types (Int(..))
import GHC.Prim (Int#)
import Common
import qualified Syntax as S


--------------------------------------------------------------------------------

-- TODO: optimize layout using direct unboxed tuples.
data Closure = Closure (# Val -> Val | (# Env, Int#, S.Tm #) #)

pattern Fun f = Closure (# f | #)

pattern Close env l t <- Closure (# | (# env, (\x -> Lvl (I# x)) -> l, t #) #) where
  Close env (Lvl (I# l)) t = Closure (# | (# env, l, t #) #)
{-# complete Fun, Close #-}

data Env = Nil | Snoc Env ~Val

data RigidHead
  = RHLocalVar Lvl
  | RHPostulate Lvl
  | RHRefl Ty Val
  | RHSym Val Val Val Val
  | RHAp Val Val Val Val Val Val
  | RHTrans Val Val Val Val Val Val
  | RHExfalso S.U Val Val
  | RHCoe Val Val Val Val

data FlexHead
  -- blocking on Meta
  = FHMeta Meta
  | FHCoeRefl Meta Val Val Val Val

  -- blocking on UMax
  | FHCoeUMax S.UMax Val Val Val Val
  | FHEqUMax S.UMax Val Val Val

data UnfoldHead    -- TODO: unpack this
  = UHMeta Meta
  | UHTopDef Lvl

-- Blocking on Val in nested ways.
data Spine
  = SNil
  | SApp Spine Val S.U Icit

  | SProj1 Spine
  | SProj2 Spine
  | SProjField Spine Name Int

  | SCoeSrc Spine Val Val Val  -- netural source type
  | SCoeTgt Val Spine Val Val   -- neutral target type
  | SCoeComp Val Val Val Spine   -- composition blocking on neutral coerced value

  | SEqType Spine Val Val
  | SEqSetLhs Spine Val
  | SEqSetRhs Val Spine

type Ty = Val
data Val
  -- Rigidly stuck values
  = Rigid RigidHead Spine

  -- Flexibly stuck values
  | Flex FlexHead Spine

  -- Non-deterministic values
  | Unfold UnfoldHead Spine ~Val -- unfolding choice (top/meta)
  | Eq Val Val Val ~Val          -- Eq computation to non-Eq type

  -- Canonical values
  | U S.U
  | Top
  | Tt
  | Bot
  | Pair Val S.U Val S.U
  | Sg  Name      Ty S.U {-# unpack #-} Closure S.U
  | Pi  Name Icit Ty S.U {-# unpack #-} Closure
  | Lam Name Icit Ty S.U {-# unpack #-} Closure

--------------------------------------------------------------------------------

pattern SAppIS sp t       = SApp sp t S.Set  Impl
pattern SAppES sp t       = SApp sp t S.Set  Expl
pattern SAppIP sp t       = SApp sp t S.Prop Impl
pattern SAppEP sp t       = SApp sp t S.Prop Expl
pattern LamIS x a b       = Lam x Impl a S.Set  (Fun b)
pattern LamES x a b       = Lam x Expl a S.Set  (Fun b)
pattern LamIP x a b       = Lam x Impl a S.Prop (Fun b)
pattern LamEP x a b       = Lam x Expl a S.Prop (Fun b)
pattern PiES x a b        = Pi x Expl a S.Set  (Fun b)
pattern PiEP x a b        = Pi x Expl a S.Prop (Fun b)
pattern SgPP x a b        = Sg x a S.Prop (Fun b) S.Prop
pattern Meta m            = Flex (FHMeta m) SNil
pattern Set               = U S.Set
pattern Prop              = U S.Prop
pattern Var x             = Rigid (RHLocalVar x) SNil
pattern Skip env l        = Snoc env (Var l)
pattern Exfalso u a t     = Rigid (RHExfalso u a t) SNil
pattern Refl a t          = Rigid (RHRefl a t) SNil
pattern Sym a x y p       = Rigid (RHSym a x y p) SNil
pattern Trans a x y z p q = Rigid (RHTrans a x y z p q) SNil
pattern Ap a b f x y p    = Rigid (RHAp a b f x y p) SNil

andP :: Val -> Val -> Val
andP a b = Sg NNil a S.Prop (Fun (\ ~_ -> b)) S.Prop
{-# inline andP #-}

implies :: Val -> Val -> Val
implies a b = PiEP NNil a (\ ~_ -> b)
{-# inline implies #-}
