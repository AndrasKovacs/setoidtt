
module Errors where

import Control.Exception
import Text.Printf

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
  deriving (Show, Exception)

data ElabError
  = UnifyErrorWhile Tm Tm UnifyError
  | NameNotInScope Name
  | ExpectedFunction Tm
  | IcitMismatch Icit Icit

data Err = Err {
  errNames :: [Name],
  errErr   :: ElabError,
  errPos   :: Maybe SPos}

instance Show Err where
  show _ = "Error"

instance Exception Err

report :: [Name] -> ElabError -> a
report ns e = throw (Err ns e Nothing)

-- | Rethrow an `Err` with source position attached.
addSrcPos :: SPos -> IO a -> IO a
addSrcPos p act = act `catch` \case
  Err ns e Nothing -> throwIO (Err ns e (Just p))
  e                -> throwIO e


showError :: [Name] -> ElabError -> String
showError ns = \case
  UnifyErrorWhile lhs rhs e ->
    let err1 = case e of
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
    in err1 ++ printf
         ("while trying to unify\n\n" ++
         "  %s\n\n" ++
         "with\n\n" ++
         "  %s") (showTm ns lhs) (showTm ns rhs)

  NameNotInScope x ->
    "Name not in scope: " ++ x
  ExpectedFunction ty ->
    "Expected a function type, instead inferred:\n\n  " ++ showTm ns ty
  IcitMismatch i i' -> printf (
    "Function icitness mismatch: expected %s, got %s.")
    (show i) (show i')
