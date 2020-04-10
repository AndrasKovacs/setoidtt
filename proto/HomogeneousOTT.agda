
{-# OPTIONS --type-in-type --rewriting --prop --show-irrelevant --injective-type-constructors #-}

module HomogeneousOTT where

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

------------------------------------------------------------

record ΣPP (A : Prop)(B : A → Prop) : Prop where
  constructor _,_
  field
    ₁ : A
    ₂ : B ₁
open ΣPP public

_∧_ : Prop → Prop → Prop; infixr 4 _∧_
P ∧ Q = ΣPP P λ _ → Q

data True  : Prop where tt : True
data False : Prop where

record Prf (P : Prop) : Set where
  constructor prf
  field
    unprf : P
open Prf public

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------

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

postulate
  Propext : (P ≡ Q) ↦ ((P → Q) ∧ (Q → P))
  Π≡      : (((x : A₀) → B₀ x) ≡ ((x : A₁) → B₁ x)) ↦
            ΣPP (A₀ ≡ A₁) λ A₀₁ → ∀ a₀ → B₀ a₀ ≡ B₁ (coe A₀₁ a₀)
  Σ≡      : (Σ A₀ B₀ ≡ Σ A₁ B₁) ↦
            ΣPP (A₀ ≡ A₁) λ A₀₁ → ∀ a₀ → B₀ a₀ ≡ B₁ (coe A₀₁ a₀)
  Set≡    : (Set ≡ Set) ↦ True
  Prop≡   : (Prop ≡ Prop) ↦ True
  ℕ≡      : (ℕ ≡ ℕ) ↦ True
  Prf≡    : (Prf P ≡ Prf Q) ↦ (P ≡ Q)

  λ≡      : {f g : (x : A₀) → B₀ x} → (f ≡ g) ↦ (∀ x → f x ≡ g x)
  ,≡      : {t u : Σ A₀ B₀} → (t ≡ u) ↦ ΣPP (₁ t ≡ ₁ u) λ p →
                 coe {B₀ (₁ t)}{B₀ (₁ u)}(ap B₀ {₁ t}{₁ u} p) (₂ t) ≡ ₂ u
  zero≡   : (zero ≡ zero) ↦ True
  suc≡    : ∀ n m → (suc n ≡ suc m) ↦ (n ≡ m)

{-# REWRITE Propext Π≡ Σ≡ Set≡ Prop≡ ℕ≡ Prf≡ λ≡ ,≡ zero≡ suc≡ #-}

postulate
  ΠΣ≡      : (((x : A₀) → B₀ x) ≡ Σ A₁ B₁) ↦ False
  ΠSet≡    : (((x : A₀) → B₀ x) ≡ Set)     ↦ False
  ΠProp≡   : (((x : A₀) → B₀ x) ≡ Prop)    ↦ False
  Πℕ≡      : (((x : A₀) → B₀ x) ≡ ℕ)       ↦ False
  ΠPrf≡    : (((x : A₀) → B₀ x) ≡ Prf P)   ↦ False

  ΣΠ≡      : (Σ A₀ B₀ ≡ ((x : A₁) → B₁ x)) ↦ False
  ΣSet≡    : (Σ A₀ B₀ ≡ Set)               ↦ False
  ΣProp≡   : (Σ A₀ B₀ ≡ Prop)              ↦ False
  Σℕ≡      : (Σ A₀ B₀ ≡ ℕ)                 ↦ False
  ΣPrf≡    : (Σ A₀ B₀ ≡ Prf P)             ↦ False

  SetΠ≡    : (Set ≡ ((x : A₁) → B₁ x))     ↦ False
  SetΣ≡    : (Set ≡ Σ A₀ B₀)               ↦ False
  SetProp≡ : (Set ≡ Prop)                  ↦ False
  Setℕ≡    : (Set ≡ ℕ)                     ↦ False
  SetPrf≡  : (Set ≡ Prf P)                 ↦ False

  PropΠ≡    : (Prop ≡ ((x : A₁) → B₁ x))   ↦ False
  PropΣ≡    : (Prop ≡ Σ A₀ B₀)             ↦ False
  PropSet≡  : (Prop ≡ Set)                 ↦ False
  Propℕ≡    : (Prop ≡ ℕ)                   ↦ False
  PropPrf≡  : (Prop ≡ Prf P)               ↦ False

  ℕΠ≡    : (ℕ ≡ ((x : A₁) → B₁ x))         ↦ False
  ℕΣ≡    : (ℕ ≡ Σ A₀ B₀)                   ↦ False
  ℕSet≡  : (ℕ ≡ Set)                       ↦ False
  ℕProp≡ : (ℕ ≡ Prop)                      ↦ False
  ℕPrf≡  : (ℕ ≡ Prf P)                     ↦ False

  PrfΠ≡    : (Prf P ≡ ((x : A₁) → B₁ x))   ↦ False
  PrfΣ≡    : (Prf P ≡ Σ A₀ B₀)             ↦ False
  PrfSet≡  : (Prf P ≡ Set)                 ↦ False
  PrfProp≡ : (Prf P ≡ Prop)                ↦ False
  Prfℕ≡    : (Prf P ≡ ℕ)                   ↦ False

  zerosuc≡ : ∀ n → (zero  ≡ suc n)         ↦ False
  suczero≡ : ∀ n → (suc n ≡ zero)          ↦ False

{-# REWRITE ΠΣ≡ ΠSet≡ ΠProp≡ Πℕ≡ ΠPrf≡ ΣΠ≡ ΣSet≡ ΣProp≡ Σℕ≡ ΣPrf≡
            SetΠ≡ SetΣ≡ SetProp≡ Setℕ≡ SetPrf≡
            PropΠ≡ PropΣ≡ PropSet≡ Propℕ≡ PropPrf≡
            ℕΠ≡ ℕΣ≡ ℕSet≡ ℕProp≡ ℕPrf≡
            PrfΠ≡ PrfΣ≡ PrfSet≡ PrfProp≡ Prfℕ≡
#-}


------------------------------------------------------------

tr : (B : A → Set){x y : A} → x ≡ y → B x → B y
tr B p = coe (ap B p)

trP : (B : A → Prop){x y : A} → x ≡ y → B x → B y
trP B p bx = tr (λ x → Prf (B x)) p (prf bx) .unprf

sym : ∀ (a b : A) → a ≡ b → b ≡ a
sym {A} a b p = trP (λ b → b ≡ a) p (refl a)

trans : ∀ (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans {A} a b c p q = trP (λ c → a ≡ c) q p

postulate
  coecoe : ∀ p q a → coe {B}{C} p (coe {A}{B} q a) ↦ coe (trans A B C q p) a
{-# REWRITE coecoe #-}

postulate
  coeΠ : ∀ p f → coe {(x : A₀) → B₀ x}{(x : A₁) → B₁ x} p f ↦
                 (λ a₁ → let a₀ = coe {A₁}{A₀} (sym A₀ A₁ (₁ p)) a₁
                         in coe {B₀ a₀}{B₁ a₁}(₂ p a₀) (f a₀))

  coeΣ : ∀ p t → coe {Σ A₀ B₀}{Σ A₁ B₁} p t ↦
                 (coe {A₀}{A₁} (₁ p) (₁ t) ,
                  coe {B₀ (₁ t)}{B₁ (coe {A₀}{A₁} (₁ p) (₁ t))} (₂ p (₁ t)) (₂ t))

{-# REWRITE coeΠ coeΣ #-}

J : ∀ {x : A}(B : ∀ y → x ≡ y → Set)(br : B x (refl x))
    → ∀ {y} p → B y p
J {A} {x} B br {y} p = tr (λ y → ∀ p → B y p) p (λ _ → br) p

JP : ∀ {x : A}(B : ∀ y → x ≡ y → Prop)(br : B x (refl x))
    → ∀ {y} p → B y p
JP {A} {x} B br {y} p = trP (λ y → ∀ p → B y p) p (λ _ → br) p

  -- the rewrite rules fail somehow here though

  -- coe (ap (λ y → ∀ p → B y p) p) (λ _ → br) p
  --   =
  -- coe (ap (λ y → ∀ p → B y p) p .₂ refl) br


apd : ∀ {B : A → Set}(f : ∀ a → B a){x y : A}(p : x ≡ y)
      → tr B p (f x) ≡ f y
apd {A}{B} f {x}{y} p =
  trP (λ y → ∀ p → tr B p (f x) ≡ f y) p (λ _ → refl (f x)) p

------------------------------------------------------------

_+_ : ℕ → ℕ → ℕ; infixl 6 _+_
zero + b = b
suc a + b = suc (a + b)

_*_ : ℕ → ℕ → ℕ; infixl 7 _*_
zero * b  = zero
suc a * b = b + a * b

+0 : ∀ n → n + zero ≡ n
+0 zero    = tt
+0 (suc n) = +0 n

+ass : ∀ a b c → (a + b) + c ≡ a + (b + c)
+ass zero    b c = refl (b + c)
+ass (suc a) b c = +ass a b c

+comm : ∀ a b → a + b ≡ b + a
+comm zero zero       = tt
+comm zero (suc b)    = +comm zero b
+comm (suc a) zero    = +comm a zero
+comm (suc a) (suc b) =
  trans (a + suc b) (suc (a + b)) (b + suc a)
        (trans (a + suc b) (suc (b + a)) (suc (a + b))
               (+comm a (suc b))
               (sym (a + b) (b + a) (+comm a b)))
        (+comm (suc a) b)

data Vec (A : Set) : ℕ → Set where
  nil  : Vec A zero
  cons : ∀ {n} → A → Vec A n → Vec A (suc n)

postulate
  Vec≡  : ∀ n₀ n₁ → (Vec A₀ n₀ ≡ Vec A₁ n₁) ↦ ((A₀ ≡ A₁) ∧ (n₀ ≡ n₁))
  nil≡  : (nil {A} ≡ nil) ↦ True
  cons≡ : ∀ n a₀ a₁ as₀ as₁  → (cons {A}{n} a₀ as₀ ≡ cons a₁ as₁) ↦ (a₀ ≡ a₁) ∧ (as₀ ≡ as₁)
{-# REWRITE Vec≡ nil≡ cons≡ #-}

postulate
  coenil  : ∀ p → coe {Vec A₀ zero}{Vec A₁ zero} p nil ↦ nil
  coecons : ∀ n₀ n₁ p a as → coe {Vec A₀ (suc n₀)}{Vec A₁ (suc n₁)} p (cons a as) ↦
                             cons (coe (₁ p) a) (coe p as)
{-# REWRITE coenil coecons #-}

_++_ : ∀ {n m} → Vec A n → Vec A m → Vec A (n + m); infixr 4 _++_
nil       ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

-- nice!
++ass : ∀ {n m k}(xs : Vec A n)(ys : Vec A m)(zs : Vec A k)
        -- → tr (Vec A) (+ass n m k) ((xs ++ ys) ++ zs) ≡ xs ++ (ys ++ zs)
        → coe {Vec A (n + m + k)}{Vec A (n + (m + k))}(ap (Vec A) {n + m + k}(+ass n m k))
              ((xs ++ ys) ++ zs) ≡ xs ++ (ys ++ zs)
++ass nil         ys zs = refl (ys ++ zs)
++ass (cons x xs) ys zs = refl x , ++ass xs ys zs

------------------------------------------------------------

postulate
  Foo   : Set
  Bar   : Foo → Set
  foo1  : Foo
  foo2  : Foo
  fooeq : foo1 ≡ foo2
  bar   : Bar foo1

postulate
  Foo≡ : (Foo ≡ Foo) ↦ True
  Bar≡ : ∀ f₀ f₁ → (Bar f₀ ≡ Bar f₁) ↦ (f₀ ≡ f₁)
{-# REWRITE Foo≡ Bar≡ #-}

record Methods : Set where
  constructor methods
  field
    Fooᴰ   : Foo → Set
    Barᴰ   : ∀ f → Fooᴰ f → Bar f → Set
    foo1ᴰ  : Fooᴰ foo1
    foo2ᴰ  : Fooᴰ foo2
    fooeqᴰ : tr Fooᴰ fooeq foo1ᴰ ≡ foo2ᴰ
    barᴰ   : Barᴰ foo1 foo1ᴰ bar
open Methods public

module _ (M : Methods) where
  postulate
    FooEl : ∀ f → M .Fooᴰ f
    BarEl : ∀ {f}(b : Bar f) → M .Barᴰ f (FooEl f) b
    foo1β : FooEl foo1 ↦ M .foo1ᴰ
    foo2β : FooEl foo2 ↦ M .foo2ᴰ
  {-# REWRITE foo1β foo2β #-}

  postulate
    barβ  : BarEl bar ↦ M .barᴰ
  {-# REWRITE barβ #-}

  postulate
    BarElcoe : ∀ {f₀ f₁}(b₀ : Bar f₀)(p : Bar f₀ ≡ Bar f₁)
               → BarEl {f₁} (coe p b₀) ↦ coe (JP (λ f₁ p → M .Barᴰ f₀ (FooEl f₀) b₀ ≡ M .Barᴰ f₁ (FooEl f₁) (coe p b₀)) (refl (M .Barᴰ f₀ (FooEl f₀) b₀)) p) (BarEl b₀)
  {-# REWRITE BarElcoe #-}


fun : ∀ {f} → Bar f → ℕ
fun = BarEl (methods (λ _ → ℕ) (λ _ _ _ → ℕ) zero zero tt (suc zero))

test : fun (coe fooeq bar) ≡ suc zero
test = refl (suc zero)

-- for every parametrized/indexed IT:
--   coe computation rules, elim-coe rules
-- *no* strict constructor injectivity for quotient types
-- *no* strict type constructor injectivity for quotient types with sort equations

-- we don't have definitional "coe rotation" rule, but it's probably OK
