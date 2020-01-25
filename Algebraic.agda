{-# OPTIONS --rewriting #-}

open import Relation.Binary.PropositionalEquality hiding ([_])
{-# BUILTIN REWRITE _≡_ #-}

infixr 5 _∘ₘ_ _∘_
infixl 6 _[_]T _[_]
infixl 3 _▶ₘ_ _▶_ _,ₘ_ _,_

postulate
  Conₘ : Set
  Subₘ : Conₘ → Conₘ → Set

variable
  Γₘ Δₘ Σₘ Ξₘ : Conₘ
  σₘ δₘ νₘ    : Subₘ _ _

postulate
  idₘ  : Subₘ Γₘ Γₘ
  _∘ₘ_ : Subₘ Δₘ Σₘ → Subₘ Γₘ Δₘ → Subₘ Γₘ Σₘ
  idlₘ : idₘ ∘ₘ σₘ ≡ σₘ
  idrₘ : σₘ ∘ₘ idₘ ≡ σₘ
  assₘ : (σₘ ∘ₘ δₘ) ∘ₘ νₘ ≡ σₘ ∘ₘ δₘ ∘ₘ νₘ
  ∙ₘ   : Conₘ
  εₘ   : Subₘ Γₘ ∙ₘ
  ∙ηₘ  : σₘ ≡ εₘ
{-# REWRITE idlₘ idrₘ assₘ #-}

postulate
  Con : Conₘ → Set
  Sub : Con Γₘ → Con Δₘ → Subₘ Γₘ Δₘ → Set

variable
  Γ Δ Σ Ξ : Con _
  σ δ ν   : Sub _ _ _

postulate
  id  : Sub Γ Γ idₘ
  _∘_ : Sub Δ Σ σₘ → Sub Γ Δ δₘ → Sub Γ Σ (σₘ ∘ₘ δₘ)
  idl : id ∘ σ ≡ σ
  idr : σ ∘ id ≡ σ
  ass : (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
  ∙   : Con Γₘ
  ε   : (σₘ : Subₘ Γₘ Δₘ) → Sub Γ ∙ σₘ
  ∙η  : σ ≡ ε σₘ
  εid : ε (idₘ {Γₘ}) ≡ id                    -- derivable
  ε∘  : ε {_}{_}{Γ}(σₘ ∘ₘ δₘ) ≡ ε σₘ ∘ ε δₘ  -- derivable
{-# REWRITE idl idr ass εid ε∘ #-}

postulate
  Ty : Con Γₘ → Set
  Tm : (Γ : Con Γₘ) → Ty Γ → Set

variable
  A B C : Ty _
  t u v : Tm _ _

postulate
  _[_]T : Ty Δ → Sub Γ Δ σₘ → Ty Γ
  _[_]  : Tm Δ A → (σ : Sub Γ Δ σₘ) → Tm Γ (A [ σ ]T)
  [id]T : A [ id ]T ≡ A
  [∘]T  : A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T
{-# REWRITE [id]T [∘]T #-}

postulate
  _▶ₘ_ : (Γₘ : Conₘ) → Ty {Γₘ} ∙ → Conₘ
  pₘ   : Subₘ (Γₘ ▶ₘ A) Γₘ
  qₘ   : Tm {Γₘ ▶ₘ A} ∙ (A [ ε pₘ ]T)
  _,ₘ_ : (σₘ : Subₘ Γₘ Δₘ) → Tm {Γₘ} ∙ (A [ ε σₘ ]T) → Subₘ Γₘ (Δₘ ▶ₘ A)
  pₘβ  : (pₘ ∘ₘ (σₘ ,ₘ t)) ≡ σₘ
{-# REWRITE pₘβ #-}
-- + naturality

postulate
  qₘβ  : (qₘ [ ε {_}{_}{∙}(σₘ ,ₘ t) ]) ≡ {!t!} -- rewrite fail

postulate
  _▶_ : (Γ : Con Γₘ) → Ty Γ → Con Γₘ
  p   : Sub (Γ ▶ A) Γ idₘ
  q   : Tm (Γ ▶ A) (A [ p ]T)
  _,_ : (σ : Sub Γ Δ σₘ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A) σₘ
  pβ  : p ∘ (σ , t) ≡ σ
{-# REWRITE pβ #-}
postulate
  qβ  : q [ σ , t ] ≡ t
{-# REWRITE qβ #-}
-- + naturality

π₁ : Sub Γ (Δ ▶ A) σₘ → Sub Γ Δ σₘ
π₁ σ = p ∘ σ

π₂ : (σ : Sub Γ (Δ ▶ A) σₘ) → Tm Γ (A [ π₁ σ ]T)
π₂ σ = q [ σ ]
