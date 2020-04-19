{-# OPTIONS --type-in-type #-}

open import Data.Unit
open import Data.Product
open import Function

data Tel : Set where
  ∙   : Tel
  _▶_ : (A : Set) → (A → Tel) → Tel
infixl 3 _▶_

-- TelElim :

-- Cat = Σ(Obj : Set, Mor : Obj → Obj → Set, id: {i} → Mor i i,.....)

-- Universe polymorphism!
-- Tel i → U i


-- (∀ {i}(Γ : Tel i) → U (f Γ))

El : Tel → Set
El ∙       = ⊤
El (A ▶ Γ) = Σ A (El ∘ Γ)

infixr 4 _++_
_++_ : (Γ : Tel) → (El Γ → Tel) → Tel
∙       ++ Δ = Δ tt
(A ▶ Γ) ++ Δ = A ▶ λ a → Γ a ++ (λ γ → Δ (a , γ))

pair : ∀ {Γ}{Δ : El Γ → Tel}(t : El Γ) → El (Δ t) → El (Γ ++ Δ)
pair {∙}     t         u = u
pair {A ▶ Γ} (t₀ , t₁) u = t₀ , pair t₁ u
