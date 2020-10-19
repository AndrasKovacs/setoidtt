
{-# options_ghc -funbox-strict-fields #-}

module Presyntax where

import Common
import FlatParse

data Bind
  = Bind Span
  | DontBind

instance Show Bind where
  show (Bind x) = show x
  show DontBind = "_"

data TopLevel
  = Nil
  | Define Span (Maybe Tm) Tm TopLevel
  | Postulate Span Tm TopLevel
  deriving Show

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

  | Exfalso Pos (Maybe Tm) Tm
  | Eq Tm Tm
  | Refl Span (Maybe Tm) (Maybe Tm)
  | Coe Pos (Maybe Tm) (Maybe Tm) Tm Tm
  | Sym Pos (Maybe Tm) (Maybe Tm) (Maybe Tm) Tm
  | Trans Pos (Maybe Tm) (Maybe Tm) (Maybe Tm) (Maybe Tm) Tm Tm
  | Ap Pos (Maybe Tm) (Maybe Tm) Tm (Maybe Tm) (Maybe Tm) Tm

  | Hole Span
  deriving Show

-- | Get the source text spanned by a raw term.
span :: Tm -> Span
span t = Span (left t) (right t) where
  left :: Tm -> Pos
  left = \case
    Var (Span l _)      -> l
    Let l _ _ _ _       -> l
    Pi l _ _ _ _        -> l
    App t _ _           -> left t
    Sg l _ _ _          -> l
    Pair t _            -> left t
    Proj1 t _           -> left t
    Proj2 t _           -> left t
    ProjField t _       -> left t
    Lam l _  _ _        -> l
    Set (Span l _)      -> l
    Prop (Span l _)     -> l
    Top     (Span l _)  -> l
    Tt      (Span l _)  -> l
    Bot     (Span l _)  -> l
    Exfalso l _ _       -> l
    Eq t u              -> left t
    Refl (Span l _) _ _ -> l
    Coe l _ _ _ _       -> l
    Sym l _ _ _ _       -> l
    Trans l _ _ _ _ _ _ -> l
    Ap l _ _ _ _ _ _    -> l
    Hole    (Span l _)  -> l

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
    Exfalso _ _ t          -> right t
    Eq _ t                 -> right t
    Refl (Span _ r) _ t    -> maybe r right t
    Coe _ _ _ _ t          -> right t
    Sym _ _ _ _ t          -> right t
    Trans _ _ _ _ _ _ t    -> right t
    Ap _ _ _ _ _ _ t       -> right t
    Hole (Span l r)        -> r
