
module Presyntax where

-- import Common

-- data Apps
--   = ANil
--   | AApp Apps Tm NameOrIcit
--   deriving Show

-- type Ty = Tm

-- data Tm
--   = Var Name
--   | Let Name (Maybe Ty) Tm Tm

--   | Lam Name NameOrIcit (Maybe Ty) Tm
--   | Pi Name Icit Ty Ty
--   | Apps Tm Apps

--   | Set
--   | Prop

--   | Tel
--   | EmptyTel
--   | TCons Name Tm Tm

--   | Sg Tm                -- ^ Σ : Tel i → U i
--   | Pair Tm Tm           -- ^ (A : U i)(B : A → Tel j) → Σ(x:A, B x)
--   | Proj1 Tm
--   | Proj2 Tm
--   | ProjField Tm Name

--   | Src SrcPos Tm
--   | Hole
--   deriving Show

-- type Prog = [Tm]
