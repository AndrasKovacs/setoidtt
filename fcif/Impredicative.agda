
{-# OPTIONS --type-in-type --rewriting --prop --show-irrelevant --injective-type-constructors #-}

module Impredicative where

open import Data.Product
  renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit

variable
  A B C : Set
  P Q R : Prop
  P₀ P₁ : Prop
  Q₀    : P₀ → Prop
  Q₁    : P₁ → Prop
  A₀ A₁ : Set
  B₀    : A₀ → Set
  B₁    : A₁ → Set

record ΣPP (A : Prop)(B : A → Prop) : Prop where
  constructor _,_
  field
    ₁ : A
    ₂ : B ₁
open ΣPP public

record ΣSP (A : Set)(B : A → Prop) : Set where
  constructor _,_
  field
    ₁ : A
    ₂ : B ₁
open ΣSP public

_∧_ : Prop → Prop → Prop; infixr 4 _∧_
P ∧ Q = ΣPP P λ _ → Q

data True  : Prop where tt : True
data False : Prop where

record Prf (P : Prop) : Set where
  constructor prf
  field
    unprf : P
open Prf public

postulate
  _↦_ : {A : Set} → A → A → Set
infix 3 _↦_
{-# BUILTIN REWRITE _↦_ #-}

module _ {A : Set} where
  postulate
    _≡_  : A → A → Prop
    refl : ∀ a → a ≡ a
  infix 3 _≡_

postulate
  coe        : A ≡ B → A → B
  ap         : ∀ (f : A → B){x y} → x ≡ y → f x ≡ f y
  regularity : ∀ {p} → coe {A}{A} p ↦ (λ x → x)
{-# REWRITE regularity #-}

tr : ∀{A : Set}(P : A → Set){x y} → x ≡ y → P x → P y
tr {A} P {x} {y} p px = coe (ap P p) px

infixr 4 _◾_
infix 6 _⁻¹
postulate
  _◾_ : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _⁻¹ : {A : Set}{x y : A} → x ≡ y → y ≡ x
  ext : {A : Set}{B : A → Set}{f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g

--------------------------------------------------------------------------------

record NatAlg : Set where
  constructor natAlg
  field
    N : Set
    z : N
    s : N → N
open NatAlg

record NatTy (Γ : NatAlg) : Set where
  constructor natTy
  field
    N : N Γ → Set
    z : N (z Γ)
    s : ∀ {n} → N n → N (s Γ n)
open NatTy

record NatHom (Γ Δ : NatAlg) : Set where
  constructor natHom
  field
    N : N Γ → N Δ
    z : N (z Γ) ≡ z Δ
    s : ∀ n → N (s Γ n) ≡ s Δ (N n)
open NatHom

Nat : Set
Nat = ΣSP ((Γ : NatAlg) → N Γ) λ f →
      ∀ {Γ Δ}(σ : NatHom Γ Δ) → N σ (f Γ) ≡ f Δ

postulate
  Nat≡ : (n m : Nat) → ₁ n ≡ ₁ m → n ≡ m

zero : Nat
zero = z , z

suc : Nat → Nat
suc n = (λ Γ → s Γ (₁ n Γ)) , λ {Γ}{Δ} σ → s σ (₁ n Γ) ◾ ap (s Δ) (₂ n σ)

syn : NatAlg
syn = natAlg Nat zero suc

rec : (Γ : NatAlg) → NatHom syn Γ
rec Γ = natHom (λ n → ₁ n Γ) (refl _) (λ _ → refl _)

ind : (A : NatTy syn) → ∀ n → N A n
ind A n =
  let Γ  = natAlg (Σ Nat (N A)) (zero , z A) λ np → suc (₁ np) , s A (₂ np)
      (res1 , res2) = ₁ n Γ

      proj1 : NatHom Γ syn
      proj1 = natHom ₁ (refl _) (λ _ → refl _)

      lem : res1 ≡ n
      lem = ₂ n proj1 ◾ Nat≡ (₁ n syn) n (ext λ Γ → ₂ n (rec Γ))

  in tr (N A) lem res2
