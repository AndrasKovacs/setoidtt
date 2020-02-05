
module Types (
  module Types,
  module Text.Megaparsec
  ) where

import Control.Monad.Reader
import Lens.Micro.Platform
import Text.Megaparsec (SourcePos(..), unPos, initialPos)

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet        as IS
import qualified Data.Map.Strict    as M

-- Raw syntax
--------------------------------------------------------------------------------

type Name = String
data Icit = Impl | Expl deriving (Eq, Show)

icit :: Icit -> a -> a -> a
icit Impl i e = i
icit Expl i e = e

data Raw
  = RVar Name
  | RLam Name (Maybe Raw) (Either Name Icit) Raw
  | RApp Raw Raw (Either Name Icit)
  | RU
  | RPi Name Icit Raw Raw
  | RLet Name Raw Raw Raw
  | RHole
  | RSrcPos SourcePos Raw

deriving instance Show Raw

-- Types
--------------------------------------------------------------------------------

-- | Elaboration problem identifier.
type MId = Int

-- | Blocked problems.
type Blocking  = IS.IntSet
type BlockedBy = IS.IntSet

data MetaEntry
  = Unsolved Blocking ~VTy
  | Solved Val

  -- | Telescope constancy constraint. When the closure becomes constant,
  --   we unify the telescope with the empty telescope.
  | Constancy MId Spine Name Val BlockedBy

data Vals  = VNil | VDef Vals ~Val | VSkip Vals
data Types = TNil | TDef Types ~VTy | TBound Types ~VTy
type Ix    = Int
type Lvl   = Int
type Ty    = Tm
type VTy   = Val
type MCxt  = IM.IntMap MetaEntry

data NameOrigin = NOSource | NOInserted
type NameTable  = M.Map Name (NameOrigin, Lvl)

data ElabCxt = ElabCxt {
  elabCxtVals      :: Vals,
  elabCxtTypes     :: Types,
  elabCxtNameTable :: NameTable}

data UnifyCxt  = UnifyCxt {
  unifyCxtVals  :: Vals,
  unifyCxtTypes :: Types}

data Err    = Err {errErr :: ElabError, errPos :: Maybe SourcePos}
type ElabM  = ReaderT ElabCxt IO
type UnifyM = ReaderT UnifyCxt IO

data Tm
  = Var Ix
  | Let Name Ty Tm Tm

  | Pi Name Icit Ty Ty
  | Lam Name Icit Ty Tm
  | App Tm Tm Icit

  | Tel               -- Ty Γ
  | TEmpty            -- Tm Γ Tel
  | TCons Name Ty Ty  -- (A : Ty Γ) → Tm (Γ ▶ A) Tel → Tm Γ Tel
  | Rec Tm            -- Tm Γ Tel → Ty Γ

  | Tempty            -- Tm Γ (El TEmpty)
  | Tcons Tm Tm       -- (t : Tm Γ A) → Tm Γ (Δ[id, t]) → Tm Γ (El (TCons A Δ))
  | Proj1 Tm          -- Tm Γ (El (TCons A Δ)) → Tm Γ A
  | Proj2 Tm          -- (t : Tm Γ (El (TCons A Δ))) → Tm Γ (El (Δ[id, Proj₁ t]))

  | PiTel Name Ty Ty  -- (A : Tm Γ Tel) → Ty (Γ ▶ El A) → Ty Γ
  | AppTel Ty Tm Tm   -- (A : Tm Γ Tel)(t : Tm Γ (PiTel A B))(u : Tm Γ A)
                      -- → Tm Γ B[id, u]
  | LamTel Name Ty Tm -- (A : Tm Γ Tel)(t : Tm (Γ ▶ El A) B) → Tm Γ (PiTel A B)

  | U
  | Meta MId

data Spine
  = SNil
  | SApp Spine ~Val Icit
  | SAppTel ~Val Spine ~Val
  | SProj1 Spine
  | SProj2 Spine

valsLen :: Vals -> Int
valsLen = go 0 where
  go acc VNil        = acc
  go acc (VDef vs _) = go (acc + 1) vs
  go acc (VSkip vs)  = go (acc + 1) vs

spLen :: Spine -> Int
spLen = go 0 where
  go n SNil             = n
  go n (SApp sp _ _)    = go (n + 1) sp
  go n (SAppTel _ sp _) = go (n + 1) sp
  go n (SProj1 sp)      = go (n + 1) sp
  go n (SProj2 sp)      = go (n + 1) sp

data Head
  = HVar Lvl
  | HMeta MId
  deriving (Eq, Show)

data Val
  = VNe Head Spine

  | VPi Name Icit ~VTy (VTy -> VTy)
  | VLam Name Icit ~VTy (Val -> Val)
  | VU

  | VTel
  | VRec ~Val
  | VTEmpty
  | VTCons Name ~Val (Val -> Val)
  | VTempty
  | VTcons ~Val ~Val

  | VPiTel Name ~Val (Val -> Val)
  | VLamTel Name ~Val (Val -> Val)

type MetaInsertion = Bool

pattern VVar :: Lvl -> Val
pattern VVar x = VNe (HVar x) SNil

pattern VMeta :: MId -> Val
pattern VMeta m = VNe (HMeta m) SNil

data ElabError
  = SpineNonVar Tm Tm                    -- ^ lhs, rhs
  | SpineProjection
  | ScopeError MId [Name] Tm Name        -- ^ Meta, spine, rhs, offending variable
  | OccursCheck MId [Name] Tm
  | UnifyError Tm Tm
  | NameNotInScope Name
  | ExpectedFunction Tm                  -- ^ Inferred type.
  | NoNamedImplicitArg Name
  | CannotInferNamedLam
  | IcitMismatch Icit Icit
  | NonLinearSolution MId [Name] Tm Name -- ^ Meta, spine, rhs, nonlinear variable

-- Lenses
--------------------------------------------------------------------------------

makeFields ''ElabCxt
makeFields ''UnifyCxt
makeFields ''Err
