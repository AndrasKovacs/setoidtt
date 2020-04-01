
module Types (
  module Types,
  module Text.Megaparsec
  ) where

import Text.Megaparsec (SourcePos(..), unPos, initialPos)
import Lens.Micro.Platform

import qualified Data.IntMap.Strict as IM

-- Raw syntax
--------------------------------------------------------------------------------

-- | We wrap `SourcePos` to avoid printing it in `Show`.
newtype SPos = SPos SourcePos deriving (Eq, Ord, Read)
instance Show SPos where show _ = ""

type Name = String
data Icit = Impl | Expl deriving (Eq)

instance Show Icit where
  show Expl = "explicit"
  show Impl = "implicit"

icit :: Icit -> a -> a -> a
icit Impl i e = i
icit Expl i e = e

-- | Surface syntax.
data Raw
  = RVar Name                        -- ^ x
  | RLam Name (Maybe Raw) Icit Raw   -- ^ λx.t  or λ{x}.t with optional type annotation
                                     --   on x
  | RApp Raw Raw Icit                -- ^ t u  or  t {u}
  | RSet                             -- ^ Set
  | RProp                            -- ^ Prop
  | RPi Name Icit Raw Raw            -- ^ (x : A) → B  or  {x : A} → B
  | RLet Name Raw Raw Raw            -- ^ let x : A = t in u
  | RHole                            -- ^ _
  | RSrcPos SPos Raw                 -- ^ source position annotation, added by parsing

  | RTop
  | RTt
  | RBot                             -- ^ ⊥ : Prop
  | RExfalso                         -- ^ exfalso : {A : Set} → ⊥ → A
  | REq
  | RRfl
  | RCoe
  | RSym
  | RAp
deriving instance Show Raw


-- Types
--------------------------------------------------------------------------------

-- | Meta identifier
type MId = Int

data MetaEntry
  = Unsolved ~VTy U
  | Solved Val

-- | A partial mapping from levels to levels. Undefined domain represents
--   out-of-scope or "illegal" variables.
type Renaming = IM.IntMap Lvl

-- | Explicit strengthening. We use this for pruning and checking meta solution
--   candidates.
data Str = Str {
  _strDom :: Lvl,        -- ^ size of renaming domain
  _strCod :: Lvl,        -- ^ size of renaming codomain
  _strRen :: Renaming,   -- ^ partial renaming
  _strOcc :: Maybe MId   -- ^ meta for occurs checking
  }

-- | Lift over a bound variable.
liftStr :: Str -> Str
liftStr (Str c d r occ) = Str (c + 1) (d + 1) (IM.insert d c r) occ

-- | Skip a bound variable.
skipStr :: Str -> Str
skipStr (Str c d r occ) = Str c (d + 1) r occ

-- | Value environment. `VSkip` skips over a bound variable.
data Vals  = VNil | VDef Vals ~Val | VSkip Vals

-- | Type environment.
data Types = TNil | TDef Types ~VTy U | TBound Types ~VTy U

type Ix    = Int
type Lvl   = Int
type Ty    = Tm
type VTy   = Val
type MCxt  = IM.IntMap MetaEntry
type UCxt  = IM.IntMap (Maybe U)
type UId   = Int

-- | Extending `Types` with any type.
pattern TSnoc :: Types -> VTy -> U -> Types
pattern TSnoc as a un <- ((\case TBound as a un -> Just (as, a, un)
                                 TDef as a un   -> Just (as, a, un)
                                 TNil           -> Nothing) -> Just (as, a, un))

lvlName :: [Name] -> Lvl -> Name
lvlName ns x = ns !! (length ns - x - 1)

-- | We need to distinguish invented names from source names, as
--   we don't want the former to shadow the latter during name lookup
--   in elaboration.
data NameOrigin =
    NOSource        -- ^ Names which come from surface syntax.
  | NOInserted      -- ^ Names of binders inserted by elaboration.


-- | Context for elaboration and unification.
data Cxt = Cxt {
  cxtVals       :: Vals,
  cxtTypes      :: Types,
  cxtNames      :: [Name],
  cxtNameOrigin :: [NameOrigin],
  cxtLen        :: Int}

data U
  = Prop
  | Set
  | UMeta MId
  deriving Show

data Tm
  = Var Ix               -- ^ x
  | Let Name Ty U Tm Tm  -- ^ let x : A : B = t in u

  | Pi Name Icit Ty U Ty  -- ^ (x : A : U) → B)  or  {x : A : U} → B
  | Lam Name Icit Ty U Tm -- ^ λ(x : A : U).t  or  λ{x : A : U}.t
  | App Tm Tm U Icit      -- ^ t u  or  t {u}, last Ty is u's universe

  -- | Sg Name Ty U Ty
  -- | Proj1 Tm U
  -- | Proj2 Tm U
  -- | Pair Tm U Tm U

  | U U
  | Meta MId          -- ^ α
  | Skip Tm           -- ^ explicit weakening (convenience feature in closing types)

  | Top
  | Tt
  | Bot
  | Eq             -- ^ {A : Set} → A → A → Prop
  | Coe U          -- ^ {A B : U i} → Eq {U i} A B → A → B
  | Rfl
  | Sym
  | Ap
  | Exfalso U

data Spine
  = SNil
  | SApp Spine ~Val U Icit
  -- | SProj1 Spine U
  -- | SProj2 Spine

valsLen :: Vals -> Int
valsLen = go 0 where
  go acc VNil        = acc
  go acc (VDef vs _) = go (acc + 1) vs
  go acc (VSkip vs)  = go (acc + 1) vs

data Axiom
  = ARfl
  | ASym
  | AAp
  | AExfalso U
  deriving (Show)

axiomToTm :: Axiom -> Tm
axiomToTm = \case
  ARfl       -> Rfl
  ASym       -> Sym
  AAp        -> Ap
  AExfalso u -> Exfalso u

data Head
  = HVar Lvl
  | HMeta MId
  | HAxiom Axiom
  | HCoe U Val Val ~Val Val

data Val
  = VNe Head Spine
  | VPi Name Icit ~VTy U (VTy -> VTy)
  | VLam Name Icit ~VTy U (Val -> Val)
  | VU U
  | VTop
  | VTt
  | VBot
  | VEq Val Val Val

pattern VSet           = VU Set
pattern VProp          = VU Prop
pattern VVar x         = VNe (HVar x) SNil
pattern VMeta m        = VNe (HMeta m) SNil
pattern VAxiom ax      = VNe (HAxiom ax) SNil
pattern AppSI t u      = App t u Set Impl
pattern AppSE t u      = App t u Set Expl
pattern AppPI t u      = App t u Prop Impl
pattern AppPE t u      = App t u Prop Expl
pattern VLamIS x a b   = VLam x Impl a Set b
pattern VLamES x a b   = VLam x Expl a Set b
pattern VLamIP x a b   = VLam x Impl a Prop b
pattern VLamEP x a b   = VLam x Expl a Prop b
pattern VPiIS x a b    = VPi x Impl a Set b
pattern VPiES x a b    = VPi x Expl a Set b
pattern VPiIP x a b    = VPi x Impl a Prop b
pattern VPiEP x a b    = VPi x Expl a Prop b

tExfalso u a t   = App (Exfalso u `AppSI` a) t u Expl
tEq      a t u   = Eq  `AppSI`  a `AppSE`  t `AppSE`  u
tRfl     a t     = Rfl `AppSI`  a `AppSI`  t
tCoe u a b p t   = App (Coe u `AppSI`  a `AppSI`  b `AppPE`  p) t u Expl
tSym a x y p     = Sym `AppSI`  a `AppSI`  x `AppSI`  y `AppPE`  p
tAp  a b f x y p = Ap  `AppSI`  a `AppSI`  b `AppSE`  f `AppSI`  x `AppSI`  y
                       `AppPE`  p

-- Lenses
--------------------------------------------------------------------------------

makeFields ''Cxt
makeFields ''Str
