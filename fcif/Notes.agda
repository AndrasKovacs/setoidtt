{-# OPTIONS --type-in-type #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality

Graph : Set
Graph = Σ Set (λ A → A → A → Set)

Hom : Graph → Graph → Set
Hom (A , R) (A' , R') = Σ (A → A') λ f → (∀ {a a'} → R a a' → R' (f a) (f a'))

Id : ∀{A} → Hom A A
Id {A , R} = (λ a → a) , λ f → f

Comp : ∀ {A B C} → Hom B C → Hom A B → Hom A C
Comp (F , R) (F' , R') = (λ a → F (F' a)) , λ f → R (R' f)

Idl : ∀ {A B}{F : Hom A B} → Comp F (Id {A}) ≡ F
Idl = {!!}

-- let Id : {C : Cat} → Functor C C
--  = (λ i. i, (λ f. f, (refl, (refl, tt)))) in

-- let Comp : {C D E : Cat} → Functor D E → Functor C D → Functor C E
--  = λ F G.
--    (λ i. F.Obj (G.Obj i) ,(
--     λ f. F.Mor (G.Mor f) ,(
--     trans (ap (F.Mor) (G.id)) (F.id) ,(
--     trans (ap (F.Mor) (G.comp)) (F.comp) ,tt
--     )))) in
