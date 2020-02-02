{-# OPTIONS --type-in-type #-}

id : {A : Set} → A → A
id x = x

foo = λ {A : Set}(x : A) → x

kek = let x = foo in x

-- foo = λ {A}{B : Set} x (y : B) → id {A} x

bar = (λ {A : Set} {B : Set} (x : A)(y : B) → x) Set Set




-- open import Data.Product
--   renaming (proj₁ to ₁; proj₂ to ₂)

-- record ⊤ {i} : Set i where
--   constructor tt

-- open import Relation.Binary.PropositionalEquality
--   renaming (subst to tr; cong to ap)

-- data Bool : Set where true false : Bool

-- infixr 4 _▶_

-- -- foobar
-- id : {A : Set} → A → A
-- id x = x

-- data Tel : Set₁ where
--   ∙   : Tel
--   _▶_ : (A : Set) → (A → Tel) → Tel

-- Rec : Tel → Set₁
-- Rec ∙       = ⊤
-- Rec (A ▶ Δ) = Σ A (λ a → Rec (Δ a))

-- Π* : (Δ : Tel) → (Rec Δ → Set) → Set₁
-- Π* Δ B = (x : Rec Δ) → B x

-- app : ∀ {Δ B} → Π* Δ B → (x : Rec Δ) → B x
-- app f = f

-- lam : ∀ {Δ B} → ((x : Rec Δ) → B x) → Π* Δ B
-- lam f = f

-- -- eq1 : ∀ {A Δ B} → app {A ▶ Δ}{B} {!!} {!!} ≡ {!!}
