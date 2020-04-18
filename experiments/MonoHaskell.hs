
{-# language
  MagicHash, UnboxedTuples, BangPatterns, ScopedTypeVariables, DeriveAnyClass,
  RankNTypes, DeriveFunctor, UnboxedSums, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, FunctionalDependencies, UnicodeSyntax,
  NoImplicitPrelude,
  PatternSynonyms, DataKinds, PolyKinds, TypeFamilies #-}


import Data.Kind
import GHC.Types
import GHC.Prim

class Num (a ∷ TYPE r) where
  add ∷ a → a → a
  mul ∷ a → a → a

-- ehhhh
class IsList (r ∷ RuntimeRep) where
  data List (a ∷ TYPE r) ∷ Type
  nil    ∷ ∀ (a ∷ TYPE r). List a
  cons   ∷ ∀ (a ∷ TYPE r). a → List a → List a
  uncons ∷ ∀ (a ∷ TYPE r) r' (b ∷ TYPE r'). List a → (a → List a → b) → (() -> b) → b

instance IsList LiftedRep where
  data List a = Nil | Cons a (List a)
  nil    = Nil
  cons   = Cons
  uncons Nil         c n = n ()
  uncons (Cons a as) c n = c a as

-- {-# inline map #-}
-- map ∷ ∀ r r' (a ∷ TYPE r)(b ∷ TYPE r'). (IsList r, IsList r') ⇒ (a → b) → List a → List b
-- map f as = uncons as
--   (\a as -> cons (f a) (map f as))
--   (\_ -> nil)
