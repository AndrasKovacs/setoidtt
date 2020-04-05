{-# options_ghc -Wno-orphans #-}

module Pretty (showTm, showTopTm, showTm', showVal) where

import Lens.Micro.Platform
import qualified Data.IntSet as IS
import Types
import Evaluation

-- | We specialcase printing of top lambdas, since they are usually used
--   to postulate stuff. We use '*' in a somewhat hacky way to mark
--   names bound in top lambdas, so that later we can avoid printing
--   them in meta spines.
topLams :: Bool -> String -> String -> [Name] -> Tm -> ShowS
topLams p pre post ns (Lam (fresh ns -> x) i a _ t) =
  showParen p (
    (pre++)
  . icit i bracket parens (
         ((if null x then "_" else x)++) . (" : "++) . go False ns a)
  . topLams False "\n " ".\n\n" (('*':x):ns) t) -- note the '*'
topLams _ pre post ns t = (post++) . go False ns t

fresh :: [Name] -> Name -> Name
fresh _ "_" = "_"
fresh ns n | elem n ns = fresh ns (n++"'")
           | otherwise = n

goU :: Bool -> U -> ShowS
goU p Prop       = ("Prop"++)
goU p Set        = ("Set"++)
goU p (UMeta x)  = (("U?"++show x)++)
goU p (UMax xs)  = (("UMax "++ show (IS.toList xs))++)

goVar :: [Name] -> Ix -> ShowS
goVar ns x = case ns !! x of
  '*':n -> (n++)
  n     -> (n++)

goArg :: [Name] -> Tm -> Icit -> ShowS
goArg ns t i = icit i (bracket (go False ns t)) (go True ns t)

goLamBind :: Name -> Icit -> ShowS
goLamBind x i = icit i bracket id ((if null x then "_" else x) ++)

bracket s = ('{':).s.('}':)
parens  s = ('(':).s.(')':)

goLam :: [Name] -> Tm -> ShowS
goLam ns (Lam (fresh ns -> x) i a _ t) = (' ':) . goLamBind x i . goLam (x:ns) t
goLam ns t = (". "++) . go False ns t

goPiBind :: [Name] -> Name -> Icit -> Tm -> U -> ShowS
goPiBind ns x i a au =
  icit i bracket (showParen True) (
    (x++) . (" : "++) . go False ns a
    -- . (" : "++) . (show au++)
    )

goPi :: [Name] -> Bool -> Tm -> ShowS
goPi ns p (Pi (fresh ns -> x) i a au b)
  | x /= "_" = goPiBind ns x i a au . goPi (x:ns) True b
  | otherwise =
     (if p then (" → "++) else id) .
     go (case a of App{} -> False; Sg{} -> False; _ -> True) ns a .
     (" → "++) . go False (x:ns) b

goPi ns p t = (if p then (" → "++) else id) . go False ns t

isMetaSp :: Tm -> Bool
isMetaSp Meta{}         = True
isMetaSp (App t _ _ _)  = isMetaSp t
isMetaSp _              = False

goMetaSp :: [Name] -> Tm -> ShowS
goMetaSp ns (App t (Var x) _ i) | '*':_ <- ns !! x =
  goMetaSp ns t
goMetaSp ns (App t u _ i)    =
  goMetaSp ns t . (' ':) . goArg ns u i
goMetaSp ns (Meta m) = ("?"++).(show m++)
goMetaSp _ _ = error "impossible"

goSp :: [Name] -> Tm -> ShowS
goSp ns (App t u _ i) = goSp ns t . (' ':) . goArg ns u i
goSp ns t = go True ns t


go :: Bool -> [Name] -> Tm -> ShowS
go p ns = \case
  Var x -> goVar ns x
  Meta m -> ("?"++).(show m++)
  Let (fresh ns -> x) a _ t u ->
    ("let "++) . (x++) . (" : "++) . go False ns a . ("\n    = "++)
    . go False ns t  . ("\nin\n"++) . go False (x:ns) u
  t@App{} | isMetaSp t -> showParen p (goMetaSp ns t)
          | otherwise  -> showParen p (goSp     ns t)

  Lam (fresh ns -> x) i a _ t -> showParen p (("λ "++) . goLamBind x i . goLam (x:ns) t)
  t@Pi{}         -> showParen p (goPi ns False t)
  U u            -> goU p u
  Skip t         -> go p ("_":ns) t
  Top            -> ("⊤"++)
  Tt             -> ("tt"++)
  Bot            -> ("⊥"++)
  Exfalso u      -> ("exfalso"++)
  Eq             -> ("Eq"++)
  Refl           -> ("refl"++)
  Coe u          -> ("coe"++)
  Sym            -> ("sym"++)
  Ap             -> ("ap"++)

  Sg (fresh ns -> x) a au b bu
    | x == "_"  ->
       showParen p (
       go (case a of Sg{} -> True;Pi{} -> True;_ -> False) ns a .(" × "++).
       go (case b of Pi{} -> True; _ -> False) (x:ns) b)
    | otherwise ->
      showParen p
        (parens ((x++).(" : "++).go False ns a)
         .(" × "++). go (case b of Pi{} -> True; _ -> False) (x:ns) b)

  Proj1 t tu     -> ("π₁ "++).go True ns t
  Proj2 t tu     -> ("π₂ "++).go True ns t
  Pair t tu u uu -> parens (go False ns t . (", "++) . go False ns u)

showTm :: [Name] -> Tm -> String
showTm ns t = go False ns t []
-- showTm ns t = show t
-- deriving instance Show Tm
instance Show Tm where show = showTopTm

showTopTm :: Tm -> String
showTopTm t = topLams False "λ" "" [] t []

showTm' :: Cxt -> Tm -> String
showTm' cxt t = showTm (cxt^.names) t

showVal :: Cxt -> Val -> String
showVal cxt v = showTm' cxt (quote (cxt^.len) v)
