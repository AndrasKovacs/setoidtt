
-- deriving telescopes and strict curried functions

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat

record ⊤ {i} : Set i where
  constructor tt

Tel' : ℕ → Set₁
Tel' zero    = ⊤
Tel' (suc n) = Σ Set λ A → A → Tel' n

Tel : Set₁
Tel = ∃ Tel'

pattern ε       = (zero , _)
pattern _▶_ A Γ = (suc _ , A , Γ)

Rec : Tel → Set
Rec ε       = ⊤
Rec (A ▶ Γ) = Σ A λ a → Rec (_ , Γ a)

Πᶜ : (Δ : Tel) → (Rec Δ → Set) → Set
Πᶜ ε       B = B tt
Πᶜ (A ▶ Δ) B = (x : A) → Πᶜ (_ , Δ x) λ δ → B (x , δ)

app : ∀ {Δ B} → Πᶜ Δ B → (δ : Rec Δ) → B δ
app {ε}     f x         = f
app {A ▶ Δ} f (x₀ , x₁) = app (f x₀) x₁

lam : ∀ {Δ B} → ((δ : Rec Δ) → B δ) → Πᶜ Δ B
lam {ε}     f = f tt
lam {A ▶ Δ} f = λ x → lam λ δ → f (x , δ)

β : ∀ Δ B (f : (δ : Rec Δ) → B δ) δ → app {Δ}{B}(lam f) δ ≡ f δ
β ε       B f δ       = refl
β (A ▶ Δ) B f (x , δ) = β (_ , Δ x) _ (λ δ → f (x , δ)) δ

postulate
  ext : ∀ {i j}{A : Set i}{B : A → Set j}{f g : ∀ a → B a}
        → (∀ x → f x ≡ g x)
        → f ≡ g

η : ∀ Δ B f → lam {Δ}{B} (app f) ≡ f
η ε       B f = refl
η (A ▶ Δ) B f = ext λ x → η (_ , Δ x) _ (f x)
