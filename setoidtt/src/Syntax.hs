
module Syntax where

import qualified Data.IntSet as IS
import Common

type Ty = Tm
type UMax = IS.IntSet

data U
  = Set
  | UMax UMax   -- ^ Maximum of a set of universe metas. Empty set = Prop.
  deriving Show

pattern Prop :: U
pattern Prop <- ((\case UMax xs -> IS.null xs; _ -> False) -> True) where
  Prop = UMax mempty

instance Semigroup U where
  UMax as <> UMax bs = UMax (as <> bs)
  _       <> _       = Set
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
  | MetaVar Meta
  | Let Name Ty U Tm Tm

  | Pi Name Icit Ty U Ty  -- ^ (x : A : U) → B)  or  {x : A : U} → B
  | Lam Name Icit Ty U Tm -- ^ λ(x : A : U).t  or  λ{x : A : U}.t
  | App Tm Tm U Icit      -- ^ t u  or  t {u}, last Ty is u's universe

  | Sg Name Ty U Ty U
  | Proj1 Tm U
  | Proj2 Tm U
  | ProjField Tm Name Int U
  | Pair Tm U Tm U

  | U U            -- ^ U u : Set
  | Top            -- ^ Top : Prop
  | Tt             -- ^ Tt  : Top
  | Bot            -- ^ Bot : Prop

  -- TODO: all of these should be fully applied, eta-expanded in elaboration
  -- clearly being fully applied is the most common, and it's way more compact & faster
  -- to store that way
  | Eq             -- ^ {A : Set} → A → A → Prop
  | Coe            -- ^ {A B : Set} → Eq {Set} A B → A → B
  | Refl           -- ^ {A : Set}(x : A) → Eq x x
  | Sym            -- ^ {A : Set}{x y : A} → Eq x y → Eq y x
  | Trans          -- ^ {A : Set}{x y z : A} → Eq x y → Eq y z → Eq x z
  | Ap             -- ^ {A B : Set}(f : A → B){x y : A} → Eq x y → Eq (f x) (f y)
  | Exfalso U      -- ^ {A : U i} → Bot → A
