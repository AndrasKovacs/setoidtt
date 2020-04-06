
module Errors where

import Control.Exception
import Text.Printf

import Lens.Micro.Platform
import Types
import Pretty

--------------------------------------------------------------------------------

data SpineError
  = SpineNonVar
  | SpineProjection
  | NonLinearSpine Lvl
  deriving (Show, Exception)

data StrengtheningError
  = ScopeError Lvl
  | OccursCheck
  deriving (Show, Exception)

data UnifyError
  = UnifyError [Name] Tm Tm
  | SpineError [Name] Tm Tm SpineError
  | StrengtheningError [Name] Tm Tm StrengtheningError
  | RelevantMetaInIrrelevantMode MId
  | ProjMismatch
  deriving (Show, Exception)

data ElabError
  = UnifyErrorWhile Tm Tm UnifyError
  | NameNotInScope Name
  | ExpectedFunction Tm
  | ExpectedType Tm Tm
  | IcitMismatch Icit Icit
  | ExpectedSg Tm
  | UnappliedProj

data Err = Err {
  errNames :: [Name],
  errErr   :: ElabError,
  errPos   :: Maybe SPos}

instance Show Err where
  show _ = "Error"

instance Exception Err

report :: Cxt -> ElabError -> a
report cxt e = throw (Err (cxt^.names) e Nothing)

-- | Rethrow an `Err` with source position attached.
addSrcPos :: SPos -> IO a -> IO a
addSrcPos p act = act `catch` \case
  Err ns e Nothing -> throwIO (Err ns e (Just p))
  e                -> throwIO e

showUnifyError :: [Name] -> UnifyError -> String
showUnifyError ns e = case e of
  UnifyError ns lhs rhs -> printf
    ("Cannot unify\n\n" ++
     "  %s\n\n" ++
     "with\n\n" ++
     "  %s\n\n")
    (showTm ns lhs) (showTm ns rhs)
  StrengtheningError ns lhs rhs e -> case e of
    ScopeError x -> printf (
      "Variable %s is out of scope in equation\n\n" ++
      "  %s =? %s\n\n")
      (lvlName ns x) (showTm ns lhs) (showTm ns rhs)
    OccursCheck -> printf (
      "Meta occurs cyclically in its solution candidate in equation:\n\n" ++
      "  %s =? %s\n\n")
      (showTm ns lhs) (showTm ns rhs)
  SpineError ns lhs rhs e -> case e of
    SpineNonVar -> printf (
      "Non-bound-variable value in meta spine in equation:\n\n" ++
      "  %s =? %s\n\n")
      (showTm ns lhs) (showTm ns rhs)
    SpineProjection ->
      "Projection in meta spine\n\n"
    NonLinearSpine x -> printf
      ("Nonlinear variable %s in meta spine in equation\n\n" ++
       "  %s =? %s\n\n")
      (lvlName ns x)
      (showTm ns lhs) (showTm ns rhs)
  RelevantMetaInIrrelevantMode m ->
    error (printf "Relevant meta cannot be solved in irrelevant mode: %s" (show m))
  ProjMismatch ->
    "Mismatched Σ projections"

showError :: [Name] -> ElabError -> String
showError ns = \case
  UnifyErrorWhile lhs rhs e ->
    let err1 = showUnifyError ns e
    in err1 ++ printf
         ("while trying to unify\n\n" ++
         "  %s\n\n" ++
         "with\n\n" ++
         "  %s") (showTm ns lhs) (showTm ns rhs)
  NameNotInScope x ->
    "Name not in scope: " ++ x
  ExpectedFunction ty ->
    "Expected a function type, instead inferred:\n\n  " ++ showTm ns ty
  ExpectedType a un -> printf (
    "Expected type Set or Prop for expression:\n\n" ++
    "  %s\n\n" ++
    "inferred type\n\n" ++
    "  %s") (showTm ns a) (showTm ns un)
  IcitMismatch i i' -> printf (
    "Function icitness mismatch: expected %s, got %s.")
    (show i) (show i')
  ExpectedSg ty ->
    "Expected a pair type, instead inferred:\n\n  " ++ showTm ns ty
  UnappliedProj ->
    "Projections must be fully applied."
