
module Syntax where

import qualified Data.IntSet as IS
import Common

type Ty = Tm
type UMax = IS.IntSet

data U
  = Set
  | Prop
  | UMax UMax   -- ^ Maximum of a non-empty set of universe metas.
  deriving (Eq, Show)

instance Semigroup U where
  u <> u' = case u of
    Set     -> Set
    Prop    -> u'
    UMax xs -> case u' of
      Set      -> Set
      Prop     -> UMax xs
      UMax xs' -> UMax (xs <> xs')
  {-# inline (<>) #-}

instance Monoid U where
  mempty = Prop
  {-# inline mempty #-}

pattern UVar :: UMeta -> U
pattern UVar x <- ((\case UMax xs -> IS.toList xs;_ -> []) -> [UMeta -> x]) where
  UVar (UMeta x) = UMax (IS.singleton x)

data Tm
  = LocalVar Ix
  | TopDef Lvl
  | Postulate Lvl
  | Meta Meta
  | Let Name Ty U Tm Tm

  | Pi Name Icit Ty U Ty   -- ^ (x : A : U) → B)  or  {x : A : U} → B
  | Lam Name Icit Ty U Tm  -- ^ λ(x : A : U).t  or  λ{x : A : U}.t
  | App Tm Tm U Icit       -- ^ t u  or  t {u}, last Ty is u's universe

  | Sg Name Ty U Ty U
  | Proj1 Tm
  | Proj2 Tm
  | ProjField Tm Name Int
  | Pair Tm U Tm U

  | U U            -- ^ U u : Set
  | Top            -- ^ Top : Prop
  | Tt             -- ^ Tt  : Top
  | Bot            -- ^ Bot : Prop

  | Eq Ty Tm Tm              -- ^ {A : Set} → A → A → Prop
  | Coe Ty Ty Tm Tm          -- ^ {A B : Set} → Eq {Set} A B → A → B
  | Refl Ty Tm               -- ^ {A : Set}(x : A) → Eq x x
  | Sym Ty Tm Tm Tm          -- ^ {A : Set}{x y : A} → Eq x y → Eq y x
  | Trans Ty Tm Tm Tm Tm Tm  -- ^ {A : Set}{x y z : A} → Eq x y → Eq y z → Eq x z
  | Ap Ty Ty Tm Tm Tm Tm     -- ^ {A B : Set}(f : A → B){x y : A} → Eq x y → Eq (f x) (f y)
  | Exfalso U Ty Tm          -- ^ {A : U i} → Bot → A
