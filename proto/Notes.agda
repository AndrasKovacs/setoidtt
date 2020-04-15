{-# OPTIONS --type-in-type #-}

module Notes where

open import Data.Product
open import Relation.Binary.PropositionalEquality

module Parameters where
  Graph : Set
  Graph = Σ Set (λ A → A → A → Set)

  Hom : Graph → Graph → Set
  Hom (A , R) (A' , R') =
    Σ (A → A') λ f
    → (∀ {a a' fa fa'} → fa ≡ f a → fa' ≡ f a' → R a a' → R' fa fa')

  Id : ∀{A} → Hom A A
  Id {A , R} = (λ a → a) , λ {refl refl f → f}

  Comp : ∀ {A B C} → Hom B C → Hom A B → Hom A C
  Comp (F , R) (F' , R') =
    (λ a → F (F' a)) , λ {refl refl f → R refl refl  (R' refl refl f)}

  -- inferable
  Idl : ∀ {A B}{F : Hom A B} → Comp F (Id {A}) ≡ F
  Idl = {!!}

module Indices where

  Graph : Set
  Graph = Σ Set (λ A → A → A → Set)

  Hom : Graph → Graph → Set               -- injective record types
  Hom (A , R) (A' , R') =
    Σ (A → A') λ f
    → (∀ {a a'} → R a a' → R' (f a) (f a'))
    × (R' ≡ R')

  Id : ∀{A} → Hom A A
  Id {A , R} = (λ a → a) , (λ f → f) , refl

  Comp : ∀ {A B C} → Hom B C → Hom A B → Hom A C
  Comp (F , R , _) (F' , R' , _) =
    (λ a → F (F' a)) , (λ f → R (R' f)) , refl

  Idl : ∀ {A B}{F : Hom A B} → Comp F (Id {A}) ≡ F
  Idl = {!!}
