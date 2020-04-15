{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# language RankNTypes, ScopedTypeVariables, TypeInType, DerivingVia, GADTs,
             LambdaCase, PatternSynonyms, MagicHash, UnboxedTuples #-}
{-# options_ghc -Wincomplete-patterns #-}

import Unsafe.Coerce
import Data.Coerce

data Nat = Z | S Nat

newtype Lvl (e :: Nat) = Lvl Int
  deriving (Show, Num, Eq) via Int

newtype Ix (e :: Nat) = Ix Int
  deriving (Show, Num, Eq) via Int

pattern IZ :: forall n. Ix (S n)
pattern IZ = Ix 0

pattern IS :: forall n. Ix n -> Ix (S n)
pattern IS x <- ((\case (Ix x) | x /= 0 -> Just (Ix (x - 1)); _ -> Nothing) -> Just x)
{-# complete IZ, IS #-}

wkLvl :: Lvl n -> Lvl (S n)
wkLvl = coerce

wkVal :: Val n -> Val (S n)
wkVal = unsafeCoerce

vVar :: Env n -> Ix n -> Val n
vVar Nil         x      = case x of
vVar (Def env v) IZ     = v
-- vVar (Def env v) (IS x) = undefined
vVar (Skip env)  IZ     = undefined
vVar (Skip env)  (IS x) = wkVal (vVar env x)

data Tm (e :: Nat) where
  Var :: Ix e -> Tm e
  Lam :: String -> Tm (S e) -> Tm e
  App :: Tm e -> Tm e -> Tm e

data Env (e :: Nat) where
  Nil  :: Env Z
  Def  :: Env e -> Val e -> Env e
  Skip :: Env e -> Env (S e)

data Val (e :: Nat) where
  VVar :: Lvl e -> Val e
  VApp :: Val e -> Val e -> Val e
  VLam :: String -> (Val e -> Val e) -> Val e

-- eval :: Env e -> Tm e -> Val e
-- eval env = \case
--   Var x   -> vVar env x
--   Lam x t -> VLam x (\v -> eval undefined t)
--   App t u -> _
