

module Pretty where

import Data.List (intercalate)
import Text.Printf

import Types

-- | Assumption: the `[Name]` input does not have shadowing.
prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  fresh :: [Name] -> Name -> Name
  fresh ns n | elem n ns = fresh ns (n++"'")
             | otherwise = n

  goVar :: [Name] -> Ix -> ShowS
  goVar ns topX = go ns topX where
    go []     _ = (show topX++)
    go (n:ns) 0 = (n++)
    go (n:ns) x = go ns (x - 1)

  goArg :: [Name] -> Tm -> Icit -> ShowS
  goArg ns t i = icit i (bracket (go False ns t)) (go True ns t)

  goLamBind :: Name -> Icit -> ShowS
  goLamBind x i = icit i bracket id ((if null x then "_" else x) ++)

  bracket :: ShowS -> ShowS
  bracket s = ('{':).s.('}':)

  goLam :: [Name] -> Tm -> ShowS
  goLam ns (Lam (fresh ns -> x) i a t)  = (' ':) . goLamBind x i . goLam (x:ns) t
  goLam ns (LamTel(fresh ns -> x) a t) =
    (' ':) . bracket ((x++) . (" : "++) . go False ns a) . goLam (x:ns) t
  goLam ns t = (". "++) . go False ns t

  goPiBind :: [Name] -> Name -> Icit -> Tm -> ShowS
  goPiBind ns x i a =
    icit i bracket (showParen True) ((x++) . (" : "++) . go False ns a)

  goPi :: [Name] -> Bool -> Tm -> ShowS
  goPi ns p (Pi (fresh ns -> x) i a b)
    | x /= "_" = goPiBind ns x i a . goPi ns True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} -> False; AppTel{} -> False; _ -> True) ns a .
       (" → "++) . go False (x:ns) b

  goPi ns p (PiTel (fresh ns -> x) a b)
    | x /= "_" = goPiBind ns x Impl a . goPi ns True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} -> False; AppTel{} -> False; _ -> True) ns a .
       (" → "++) . go False (x:ns) b

  goPi ns p t = (if p then (" → "++) else id) . go False ns t

  go :: Bool -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var x -> goVar ns x
    Meta m -> ("?"++).(show m++)
    Let (fresh ns -> x) a t u ->
      ("let "++) . (x++) . (" : "++) . go False ns a . ("\n    = "++)
      . go False ns t  . ("\nin\n"++) . go False (x:ns) u
    App (App t u i) u' i' ->
      showParen p (go False ns t . (' ':) . goArg ns u i . (' ':) . goArg ns  u' i')
    App (AppTel _ t u) u' i' ->
      showParen p (go False ns t . (' ':) . goArg ns u Impl . (' ':) . goArg ns u' i')
    App t u i      -> showParen p (go True ns t . (' ':) . goArg ns u i)
    Lam (fresh ns -> x) i a t  -> showParen p (("λ "++) . goLamBind x i . goLam (x:ns) t)
    t@Pi{}         -> showParen p (goPi ns False t)
    U              -> ("U"++)
    Tel            -> ("Tel"++)
    TEmpty         -> ("∙"++)
    TCons "_" a as -> showParen p (go False ns a . (" ▶ "++). go False ns as)
    TCons (fresh ns -> x) a as ->
              showParen p (showParen True ((x++) . (" : "++) . go False ns a)
            . (" ▶ "++). go False (x:ns) as)
    Tempty         -> ("[]"++)
    Rec a          -> showParen p (("Rec "++) . go True ns a)
    Tcons t u      -> showParen p (go True ns t . (" ∷ "++). go False ns u)
    Proj1 t        -> showParen p (("₁ "++). go True ns t)
    Proj2 t        -> showParen p (("₂ "++). go True ns t)
    t@PiTel{}      -> showParen p (goPi ns False t)
    AppTel a (App t u i) u'  ->
      showParen p (go False ns t . (' ':) . goArg ns u i . (' ':) .
                   bracket (go False ns u' . (" : "++) . go False ns a))

    AppTel a' (AppTel a t u) u' ->
      showParen p (go False ns t . (' ':)
                   . bracket (go False ns u  . (" : "++) . go False ns a)
                   . bracket (go False ns u' . (" : "++) . go False ns a'))
    AppTel a t u ->
      showParen p (go True ns t . (' ':)
                   . bracket (go False ns u  . (" : "++) . go False ns a))
    LamTel x a t -> showParen p (("λ"++)
                   . bracket ((x++) . (" : "++) . go False ns a) . goLam ns t)

showTm :: [Name] -> Tm -> String
showTm ns t = prettyTm 0 ns t []

showError :: [Name] -> ElabError -> String
showError ns = \case
  SpineNonVar lhs rhs -> printf (
    "Non-bound-variable value in meta spine in equation:\n\n" ++
    "  %s =? %s")
    (showTm ns lhs) (showTm ns rhs)
  SpineProjection -> "Projection in meta spine"
  ScopeError m sp rhs x -> printf (
    "Variable %s is out of scope in equation\n\n" ++
    "  %s %s =? %s")
    (show x) (show m) ('[':intercalate ", " sp++"]") (showTm ns rhs)
  OccursCheck m sp rhs -> printf (
    "Meta %s occurs cyclically in its solution candidate in equation:\n\n" ++
    "  %s %s =? %s")
    (show m) ('[':intercalate ", " sp++"]") (showTm ns rhs)
  UnifyError lhs rhs -> printf
    ("Cannot unify\n\n" ++
     "  %s\n\n" ++
     "with\n\n" ++
     "  %s")
    (showTm ns lhs) (showTm ns rhs)
  NameNotInScope x ->
    "Name not in scope: " ++ x
  ExpectedFunction ty ->
    "Expected a function type, instead inferred:\n\n  " ++ showTm ns ty
  NoNamedImplicitArg x -> printf
    "No named implicit argument with name %s." x
  CannotInferNamedLam ->
    "No type can be inferred for lambda with named implicit argument."
  IcitMismatch i i' -> printf (
    "Function icitness mismatch: expected %s, got %s.")
    (show i) (show i')
  NonLinearSolution m sp rhs x -> printf
    ("Nonlinear variable %s in meta spine in equation\n\n" ++
     "  %s %s =? %s")
    (show x) (show m) ('[':intercalate ", " sp++"]") (showTm ns rhs)
