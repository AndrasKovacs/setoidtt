
{-# language Strict #-}
{-# options_ghc -funbox-strict-fields #-}

module Presyntax where

import FlatParse

data Icit
  = Impl
  | Expl
  deriving Show

data ArgInfo
  = NoName Icit
  | Named Span
  deriving Show

data Bind
  = Bind Span
  | DontBind

instance Show Bind where
  show (Bind x) = show x
  show DontBind = "_"

data Tm
  = Var Span
  | Let Pos Span (Maybe Tm) Tm Tm

  | Pi Pos Bind Icit Tm Tm
  | App Tm Tm ArgInfo
  | Lam Pos Bind ArgInfo Tm

  | Sg Pos Bind Tm Tm
  | Pair Tm Tm
  | Proj1 Tm Pos
  | Proj2 Tm Pos
  | ProjField Tm Span

  | Set     Span
  | Prop    Span
  | Top     Span
  | Tt      Span
  | Bot     Span
  | Exfalso Span
  | Eq Tm Tm
  | Refl    Span
  | Coe     Span
  | Sym     Span
  | Trans   Span
  | Ap      Span
  | Hole    Span

  deriving Show

-- | Get the source text spanned by a raw term.
span :: Tm -> Span
span t = Span (left t) (right t) where
  left :: Tm -> Pos
  left = \case
    Var (Span l _)     -> l
    Let l _ _ _ _      -> l
    Pi l _ _ _ _       -> l
    App t _ _          -> left t
    Sg l _ _ _         -> l
    Pair t _           -> left t
    Proj1 t _          -> left t
    Proj2 t _          -> left t
    ProjField t _      -> left t
    Lam l _  _ _       -> l
    Set (Span l _)     -> l
    Prop (Span l _)    -> l
    Top     (Span l _) -> l
    Tt      (Span l _) -> l
    Bot     (Span l _) -> l
    Exfalso (Span l _) -> l
    Eq t u             -> left t
    Refl    (Span l _) -> l
    Coe     (Span l _) -> l
    Sym     (Span l _) -> l
    Trans   (Span l _) -> l
    Ap      (Span l _) -> l
    Hole    (Span l _) -> l


  right :: Tm -> Pos
  right = \case
    Var (Span _ r)         -> r
    Let _ _ _ _ u          -> right u
    Pi _ _ _ _ b           -> right b
    Sg _ _ _ b             -> right b
    Pair _ u               -> right u
    Proj1 _ r              -> r
    Proj2 _ r              -> r
    ProjField _ (Span _ r) -> r
    App _ u _              -> right u
    Lam _ _ _ t            -> right t
    Set (Span _ r)         -> r
    Prop (Span _ r)        -> r
    Top     (Span _ r)     -> r
    Tt      (Span _ r)     -> r
    Bot     (Span _ r)     -> r
    Exfalso (Span _ r)     -> r
    Eq t u                 -> right u
    Refl    (Span _ r)     -> r
    Coe     (Span _ r)     -> r
    Sym     (Span _ r)     -> r
    Trans   (Span _ r)     -> r
    Ap      (Span _ r)     -> r
    Hole    (Span _ r)     -> r
