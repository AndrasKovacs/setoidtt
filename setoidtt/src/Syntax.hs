
module Syntax where

import Common

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Lvl
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

  | U U
  | Top            -- ^
  | Tt             -- ^ Tt : Top
  | Bot            -- ^
  | Eq             -- ^ {A : Set} → A → A → Prop
  | Coe            -- ^ {A B : Set} → Eq {Set} A B → A → B
  | Refl           -- ^ {A : Set}(x : A) → Eq x x
  | Sym            -- ^ {A : Set}{x y : A} → Eq x y → Eq y x
  | Trans          -- ^ {A : Set}{x y z : A} → Eq x y → Eq y z → Eq x z
  | Ap             -- ^ {A B : Set}(f : A → B){x y : A} → Eq x y → Eq (f x) (f y)
  | Exfalso U      -- ^ {A : Set U i} → Bot → A
