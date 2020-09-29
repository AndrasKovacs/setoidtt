
module Common (
    module Common
  , FlatParse.Span(..)
  ) where

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
