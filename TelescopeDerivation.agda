
open import Data.Maybe
open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

record ⊤ {i} : Set i where
  constructor tt

data ⊥ {i} : Set i where

data W {i}{j}(S : Set i) (P : S → Set j) : Set (i ⊔ j) where
  sup : ∀ s → (P s → W S P) → W S P

Tel : Set₁
Tel = W (Maybe Set) (maybe (λ A → A) ⊥)

infixr 4 _▶_
pattern ∙       = sup nothing _
pattern _▶_ A Γ = sup (just A) Γ

Rec : Tel → Set₁
Rec ∙       = ⊤
Rec (A ▶ Δ) = Σ A (λ a → Rec (Δ a))

Π : (Δ : Tel) → (Rec Δ → Set) → Set
Π ∙       B = B tt
Π (A ▶ Δ) B = (x : A) → Π (Δ x) λ δ → B (x , δ)

app : ∀ {Δ B} → Π Δ B → (δ : Rec Δ) → B δ
app {∙}     f x         = f
app {A ▶ Δ} f (x₀ , x₁) = app (f x₀) x₁

lam : ∀ {Δ B} → ((δ : Rec Δ) → B δ) → Π Δ B
lam {∙}     f = f tt
lam {A ▶ Δ} f = λ x → lam λ δ → f (x , δ)

β : ∀ Δ B (f : (δ : Rec Δ) → B δ) δ → app {Δ}{B}(lam f) δ ≡ f δ
β ∙       B f δ       = refl
β (A ▶ Δ) B f (x , δ) = β (Δ x) _ (λ δ → f (x , δ)) δ

postulate
  ext : ∀ {i j}{A : Set i}{B : A → Set j}{f g : ∀ a → B a}
        → (∀ x → f x ≡ g x)
        → f ≡ g

η : ∀ Δ B f → lam {Δ}{B} (app f) ≡ f
η ∙       B f = refl
η (A ▶ Δ) B f = ext λ x → η (Δ x) _ (f x)
