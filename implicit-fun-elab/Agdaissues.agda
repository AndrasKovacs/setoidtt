{-# OPTIONS --type-in-type #-}

module Agdaissues where

module Issue2766 where

-- record P (A : Set) (B : Set) : Set where
--   constructor _,_
--   field fst : A
--         snd : B
-- uncurry : {A B C : Set} (f : A → B → C) (p : P A B) → C
-- uncurry f p = f (P.fst p) (P.snd p)

-- argh : {A B C : Set} (f : A → B → {d : C} → C → C) (p : P A B) → {d : C} → C → C
-- argh f = uncurry (λ a b c → c)

-- yeah : {A B C : Set} (f : A → B → {d : C} → C → C) (p : P A B) → {d : C} → C → C
-- yeah f = uncurry (λ a b {_} c → c)

-- open import Data.Unit
-- open import Relation.Binary.PropositionalEquality

-- postulate
--   X : Set

-- data Kind : Set where
--   x : Kind

-- F : Kind → Set
-- F x = X

-- P : Set₁
-- P = {A : Set} → A

-- P? : Kind → Set₁
-- P? x = P

-- postulate
--   f? : ∀ {k} → P? k → F k

-- works : P → X
-- works p = f? p

-- open import Data.Bool using (Bool; true; false)
-- open import Relation.Binary.PropositionalEquality

-- T : Bool → Set₁
-- T true  = {A : Set} → A → A
-- T false = Set

-- postulate
--   g : (b : Bool) → b ≡ true → T b → Bool
--   f : (b : Bool) → T b → b ≡ true → Bool

-- works : Bool
-- works = g _ refl (λ x → x)

-- test : Bool
-- test = f _ (λ x → x) refl

-- record ⊤ : Set where
--   constructor tt

-- record Into (From : Set) (To : Set) : Set where
--   field
--     into : From → To

-- open Into

-- implicit⇒⊤ : Into ({t : ⊤} → ⊤) ⊤
-- into implicit⇒⊤ x = tt

-- tt′ : {t : ⊤} → ⊤
-- tt′ = tt

-- fine : ⊤
-- fine = into implicit⇒⊤ {!into!}

-- -- filling first hole works ok, but..
-- fine-in-order : ⊤
-- fine-in-order = into implicit⇒⊤ tt′

-- -- if we fill second one first:
-- -- ⊤ !=< ({t : ⊤} → ⊤) of type Set
-- -- when checking that the expression implicit⇒⊤ has type Into ⊤ ⊤
-- can't-fill : ⊤
-- can't-fill = into {!implicit⇒⊤!} tt′

-- -- https://github.com/agda/agda/issues/2099#issuecomment-305922361
-- module Ex1 where
--   -- simplified version
--   data Wrap (A : Set) : Set where
--     wrap : A → Wrap A

--   the : (A : Set) → A → A
--   the = λ A x → x

--   prf : Wrap ({A : Set} → A → A)
--   prf = wrap (λ {A} → the (∀{A} → A → A) (λ {A}(x : A) → x){A})


-- -- https://github.com/agda/agda/issues/2099#issuecomment-540773967
-- module Ex2 where
--   -- minimal code demonstrating issue

--   id : {A : Set} → A → A
--   id x = x

--   test : {A : Set} → A → {B : Set} → B → A
--   test = {!!} -- id (λ x y → x)





-- data Bool : Set where true false : Bool

-- Ty : Set₁
-- Ty = {T : Bool → Set} → (∀{b} → T b → T true) → T false

-- postulate
--   f : Ty

-- -- works : Ty
-- -- works g = f (λ {b} → g {b})

-- test : Ty
-- test = λ g → f g

-- const : {A B : Set} → A → B → A
-- const x y = x

-- foo : Set₁
-- foo =
--   let const' : {B A : Set} → A → B → A
--       const' = const
--   in Set

-- module Issue2099 where

--   data Wrap (A : Set) : Set where
--     wrap : A → Wrap A

--   the : (A : Set) → A → A
--   the = λ A x → x

--   prf : Wrap ({A : Set} → A → A)
--   prf = wrap (λ {A} → the (∀{A} → A → A) (λ {A}(x : A) → x){A})

-- module Issue1079 where

--   open import Agda.Builtin.Nat

--   data Dec (P : Set) : Set where
--     meh : Dec P

--   True : ∀ {P : Set} → Dec P → Set
--   True meh = Nat

--   postulate
--     fromWitness : ∀ {P : Set} {Q : Dec P} → P → True Q
--     T : Nat → Set

--   Coprime = ∀ {i} → T i

--   postulate
--     coprime? : Dec Coprime

--   bla : Coprime → True coprime?
--   bla c = {!fromWitness c!}


-- data ⊤ : Set where
--   tt : ⊤

-- flip : ∀ {t₁ t₂ t₃ : Set} → (t₁ → t₂ → t₃) → t₂ → t₁ → t₃
-- flip f x y = f y x

-- R : (∀ {a b c : Set} → {x : ⊤} → (a → b) → (b → c) → ⊤) → Set₁
-- R f =
--   let g : ∀ {a b c : Set} → (b → c) → (a → b) → ⊤
--       g = flip (f {x = tt})
--   in Set


-- (f : ∀ {a b c : Set} → {x : ⊤} → (a → b) → (b → c) → ⊤)
--   →  let g : ∀ {a b c : Set} → (b → c) → (a → b) → ⊤
--          g {a}{b}{c} = flip (f {x = tt}) -- flip (f {x = tt})
--      in Set

-- R : Set₁
-- R = (f : ∀ {a b c : Set} → {x : ⊤} → (a → b) → (b → c) → ⊤)
--   →  let g : ∀ {a b c : Set} → (b → c) → (a → b) → ⊤
--          g {a}{b}{c} = flip (f {x = tt}) -- flip (f {x = tt})
--      in Set
