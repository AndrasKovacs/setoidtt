{-# options_ghc -Wno-orphans #-}

module Pretty (showTm, showTopTm) where

import Types

-- | We specialcase printing of top lambdas, since they are usually used
--   to postulate stuff. We use '*' in a somewhat hacky way to mark
--   names bound in top lambdas, so that later we can avoid printing
--   them in meta spines.
topLams :: Bool -> String -> String -> [Name] -> Tm -> ShowS
topLams p pre post ns (Lam (fresh ns -> x) i a t) =
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
goLam ns (Lam (fresh ns -> x) i a t)  = (' ':) . goLamBind x i . goLam (x:ns) t
goLam ns (LamTel(fresh ns -> x) a t) =
  (' ':) . bracket ((x++) . (" : "++) . go False ns a) . goLam (x:ns) t
goLam ns t = (". "++) . go False ns t

goPiBind :: [Name] -> Name -> Icit -> Tm -> ShowS
goPiBind ns x i a =
  icit i bracket (showParen True) ((x++) . (" : "++) . go False ns a)

goPi :: [Name] -> Bool -> Tm -> ShowS
goPi ns p (Pi (fresh ns -> x) i a b)
  | x /= "_" = goPiBind ns x i a . goPi (x:ns) True b
  | otherwise =
     (if p then (" → "++) else id) .
     go (case a of App{} -> False; AppTel{} -> False; _ -> True) ns a .
     (" → "++) . go False (x:ns) b

goPi ns p (PiTel (fresh ns -> x) a b)
  | x /= "_" = goPiBind ns x Impl a . goPi (x:ns) True b
  | otherwise =
     (if p then (" → "++) else id) .
     go (case a of App{} -> False; AppTel{} -> False; _ -> True) ns a .
     (" → "++) . go False (x:ns) b

goPi ns p t = (if p then (" → "++) else id) . go False ns t

isMetaSp :: Tm -> Bool
isMetaSp Meta{}         = True
isMetaSp (App t _ _)    = isMetaSp t
isMetaSp (AppTel _ t _) = isMetaSp t
isMetaSp _              = False

goMetaSp :: [Name] -> Tm -> ShowS
goMetaSp ns (App t (Var x) i) | '*':_ <- ns !! x =
  goMetaSp ns t
goMetaSp ns (App t u i)    =
  goMetaSp ns t . (' ':) . goArg ns u i
goMetaSp ns (AppTel a t u) =
  goMetaSp ns t . (' ':) . bracket (go False ns u . (" : "++) . go False ns a)
goMetaSp ns (Meta m) = ("?"++).(show m++)
goMetaSp _ _ = error "impossible"

goSp :: [Name] -> Tm -> ShowS
goSp ns (App t u i) = goSp ns t . (' ':) . goArg ns u i
goSp ns (AppTel a t u) =
  goSp ns t . (' ':) . bracket (go False ns u . (" : "++) . go False ns a)
goSp ns t = go True ns t

go :: Bool -> [Name] -> Tm -> ShowS
go p ns = \case
  Var x -> goVar ns x
  Meta m -> ("?"++).(show m++)
  Let (fresh ns -> x) a t u ->
    ("let "++) . (x++) . (" : "++) . go False ns a . ("\n    = "++)
    . go False ns t  . ("\nin\n"++) . go False (x:ns) u
  t@App{} | isMetaSp t -> showParen p (goMetaSp ns t)
          | otherwise  -> showParen p (goSp     ns t)
  t@AppTel{}| isMetaSp t -> showParen p (goMetaSp ns t)
            | otherwise  -> showParen p (goSp     ns t)

  Lam (fresh ns -> x) i a t  -> showParen p (("λ "++) . goLamBind x i . goLam (x:ns) t)
  t@Pi{}         -> showParen p (goPi ns False t)
  U              -> ("U"++)
  Tel            -> ("Tel"++)
  TEmpty         -> ("ε"++)
  TCons "_" a as -> showParen p (go False ns a . (" ▷ "++). go False ns as)
  TCons (fresh ns -> x) a as ->
            showParen p (showParen True ((x++) . (" : "++) . go False ns a)
          . (" ▷ "++). go False (x:ns) as)
  Tempty         -> ("[]"++)
  Rec a          -> showParen p (("Rec "++) . go True ns a)
  Tcons t u      -> showParen p (go True ns t . (" ∷ "++). go False ns u)
  Proj1 t        -> showParen p (("π₁ "++). go True ns t)
  Proj2 t        -> showParen p (("π₂ "++). go True ns t)
  t@PiTel{}      -> showParen p (goPi ns False t)

  LamTel x a t -> showParen p (("λ"++)
                 . bracket ((x++) . (" : "++) . go False ns a) . goLam (x:ns) t)

  Skip t -> go p ("_":ns) t

showTm :: [Name] -> Tm -> String
showTm ns t = go False ns t []
-- showTm ns t = show t
-- deriving instance Show Tm
instance Show Tm where show = showTopTm

showTopTm :: Tm -> String
showTopTm t = topLams False "λ" "" [] t []
