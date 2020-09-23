{-# language Strict #-}

module Presyntax where

import FlatParse

data NamedIcit
  = Explicit            -- ^ Explicit application
  | Implicit            -- ^ Implicit application
  | NamedImplicit Span  -- ^ Named implicit application
  deriving Show

data Icit
  = Impl
  | Expl
  deriving Show

data Tm
  = Var {-# unpack #-} Span
  | Let Pos {-# unpack #-} Span (Maybe Tm) Tm Tm
  | Pi Pos {-# unpack #-} Span Icit Tm Tm
  | App Tm Tm NamedIcit
  | Lam {-# unpack #-} Span NamedIcit Tm
  | Set {-# unpack #-} Span
  | Prop {-# unpack #-} Span
  deriving Show

-- | Get the source text spanned by a raw term.
span :: Tm -> Span
span t = Span (left t) (right t) where
  left :: Tm -> Pos
  left = \case
    Var (Span l _)       -> l
    Let l _ _ _ _        -> l
    Pi l _ _ _ _         -> l
    App t _ _            -> left t
    Lam (Span l _) _ _   -> l
    Set (Span l _)       -> l
    Prop (Span l _)      -> l

  right :: Tm -> Pos
  right = \case
    Var (Span _ r)       -> r
    Let _ _ _ _ u        -> right u
    Pi _ _ _ _ b         -> right b
    App _ u _            -> right u
    Lam _ _ t            -> right t
    Set (Span _ r)       -> r
    Prop (Span _ r)      -> r
