module Main where

import Control.Exception
import System.Environment
import System.Exit
import Text.Printf

import ElabState
import Elaboration
import Errors
import EvalCxt
import Parser
import Types
import Zonk


helpMsg = unlines [
  "usage: fcif [--help|elab|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin, print elaboration output",
  "  nf     : read & elaborate expression from stdin, print its normal form",
  "  type   : read & elaborate expression from stdin, print its (normal) type"]

displayError :: String -> Err -> IO a
displayError file (Err ns err (Just (SPos (SourcePos path (unPos -> linum) (unPos -> colnum))))) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n\n" (showError ns err)
  exitSuccess
displayError file (Err _ _ Nothing) =
  error "impossible"


mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getTm = do
  let elab :: IO (Tm, Tm, Tm, U)
      elab = do
        reset
        (t, src) <- getTm
        (t, a, au) <- inferTopLams emptyCxt t `catch` displayError src
        t <- pure $ zonk VNil 0 t
        let ~nt = quote emptyCxt $ eval emptyCxt t
        let ~na = quote emptyCxt a
        pure (t, nt, na, forceU au)

  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, nt, na, u) <- elab
      putStrLn $ show nt
    ["type"] -> do
      (t, nt, na, u) <- elab
      putStrLn $ show na
    ["univ"] -> do
      (t, nt, na, u) <- elab
      putStrLn $ show u
    ["elab"] -> do
      (t, nt, na, u) <- elab
      putStrLn $ show t
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)

------------------------------------------------------------

test1 = main' "elab" $ unlines [
  "λ (Nat : Set)",
  "  (zero : Nat)",
  "  (suc : Nat → Nat)",
  "  (f : Nat → Prop)",
  "  (foo : Nat → Set). ",
  "let g : Nat → Prop = f in",
  "Set"
  ]

test = main' "nf" $ unlines [
  -- "let ₁₂ : {A : Set}{B : A → Set}{C : (a : A) → B a → Set}",
  -- " → (inp : (a : A) × (b : B a) × C a b)",
  -- " → B (₁ inp)",
  -- " = λ inp . ₁ (₂ inp) in",

  -- "let foo : ((A : Set) × A) → Set = λ Γ. ₁ Γ → ₁ Γ in",
  -- "Set"

  -- "let ₁₂ : {A : Set}{B : A → Set}{C : (a : A) → B a → Set}",
  -- "         → (inp : (a : A) × (b : B a) × C a b)",
  -- "      → B (₁ inp)",
  -- "  = λ inp. ₁ (₂ inp) in",
  -- "let ₂₂ : {A : Set}{B : A → Set}{C : (a : A) → B a → Set}",
  -- "         → (inp : (a : A) × (b : B a) × C a b)",
  -- "      → C (₁ inp) (₁₂ inp)",
  -- "  = λ inp. ₂ (₂ inp) in",
  -- "let Conᴺ : Set",
  -- "  = (N : Set) × N × (N → N) in",
  -- "let Subᴺ : Conᴺ → Conᴺ → Set",
  -- "  = λ Γ Δ. (Nᴹ : ₁ Γ → ₁ Δ) × Set in",
  -- "Set  "

  -- "(n m : _) → Eq {(A : Set) × Eq A A} n m"
  ]

test2 = main' "elab" $ unlines [
  "let foo : (p : Eq {Set} Set Prop)(A : Set) → Prop",
  "    = λ p A. coe p A in",
  "let tr : {A : Set}(B : A → Set){x y} → Eq {A} x y → B x → B y",
  "    = λ B p bx. coe (ap B p) bx in",

  "let regular : Eq (λ (A : Set)(p : Eq A A)(x : A). coe p x) (λ A p x. x) = λ _ _ _. refl in",
  "let comp : Eq (λ A B C (p : Eq {Set} A B)(q : Eq B C) x. coe q (coe p x))",
  "              (λ A B C p q x. coe (trans p q) x) = λ _ _ _ _ _ _. refl in",

  "let picoe : (A B C D : Set)(p : Eq (A → B) (C → D))(f : A → B) → C → D",
  "    = λ A B C D p f. coe p f in",

  "let foo : Eq {Set} Set Set = refl in",
  "let brek : Set × Set = coe (refl, λ _. refl) (Set, Set) in",
  "let brek2 : Set × Set = coe (ap (λ x. x) (sym (ap (λ x. x)(refl, λ _. refl)))) (Set, Set) in",
  "Set"

  ]

test4 = main' "elab" $ unlines [
  "λ(A : Set)",
  " (B : Set)",
  " (C : Set)",
  " (D : Set)",
  " (p : (p : Eq {Set} A C) × ((x : A) → Eq {Set} B D))",
  " (f : A → B)",
  " (x : C).",
  " coe {B} {D} ((π₂ p) (coe {C} {A} (sym {Set} {A} {C} (₁ p)) x)) (f (coe {C} {A}",
  " (sym {Set} {A} {C} (₁ p)) x))  "
  ]

test3 = main' "elab" $ unlines [
  -- for testing proof irrelevance
  "let EqP    : {A : Prop} → A → A → Set = λ {A} x y. (P : A → Set) → P x → P y in",
  "let reflP  : {A x} → EqP {A} x x = λ P px. px in",

  "let theP : (A : Prop) → A → A = λ A x. x in",

  "let coeS : {A B : Set}  → Eq A B → A → B = coe in",
  "let coeP : {A B : Prop} → Eq {Prop} A B → A → B = λ p. ₁ p in ",
  "let trS : {A : Set}(B : A → Set){x y} → Eq x y → B x → B y",
  "    = λ {A} B {x}{y} p bx. coe (ap B p) bx in",
  "let trP : {A : Set}(B : A → Prop){x y} → Eq x y → B x → B y",
  "    = λ {A} B {x}{y} p bx. coe (sym (sym (ap B p))) bx in",

  "let exfalsoS : {A : Set}  → ⊥ → A = exfalso in",
  "let exfalsoP : {A : Prop} → ⊥ → A = exfalso in",
  "let trans2 : {A : Set}{x y z : A} → Eq x y → Eq y z → Eq x z",
  "    = λ {_}{x} p q. trP (λ z. Eq x z) q p in",
  "let trans2 : {A : Set}{x y z : A} → Eq x y → Eq y z → Eq x z",
  "    = trans in",

  "let irrel1 : Eq (λ (f : Set → ⊤ → Set) (x : ⊤) (y : ⊤). f Set x)",
  "                (λ f x y. f Set y) =",
  "     (λ _ _ _. refl) in",

  "let trans2 : {A}{a b c d : A} → Eq a b → Eq b c → Eq c d → Eq a d",
  "    = λ p q r. trans (trans p q) r in",

  -- don't yet work!
  -- "let symex : {a b c d : Set} → Eq (a × b) (c × d) → Eq (c × d) (a × b)",
  -- "    = λ p. sym p in",

  -- "let trans3 : {a b c d e f : Set} → Eq (a × b) (c × d) → Eq (c × d) (e × f) → Eq (a × b) (e × f)",
  -- "    = λ p q r. trans (trans p q) r in",

  "let irrel2 : EqP (λ (x : ⊤)(y : ⊤). x) (λ x y. y) = reflP in",

  "let foo : (A : Set) × (A → Set) = (Set, λ A. A) in",

  "let sym2 : {A : Set}{x y : A} → Eq x y → Eq y x = sym in",

  "let foo : Eq ⊤ (⊤ × ⊤) = ((λ _. (tt, tt)), (λ _. tt)) in",
  "let bar : Eq (⊤ × ⊤) ⊤ = sym {Prop} {⊤}{⊤ × ⊤} foo in",

  -- type equality example
  "let bar  : Eq (Set → Set) (Set → Set) = refl {Set}{Set → Set} in",
  "let bar2 : Eq (Set → Set) (Set → Set) = (tt, λ_.tt) in",
  "let bar3 : EqP bar bar2 = reflP in",

  "let foo : Eq (Eq Set Prop) ⊥ = refl {Prop}{⊥} in",


  "Set"
  ]
