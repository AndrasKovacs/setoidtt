module Main where

import Text.Printf
import Control.Exception
import System.Exit
import System.Environment

import Types
import Evaluation
import Elaboration
import Errors
import Parser
import ElabState
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
        t <- pure $ zonk VNil t
        let ~nt = quote 0 $ eval VNil t
        let ~na = quote 0 a
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

test2 = main' "elab" $ unlines [
  -- for testing proof irrelevance
  "let EqP    : {A : Prop} → A → A → Set = λ {A} x y. (P : A → Set) → P x → P y in",
  "let reflP  : {A x} → EqP {A} x x = λ P px. px in",

  "let coeS : {A B : Set}  → Eq A B → A → B = coe in",
  "let coeP : {A B : Prop} → Eq {Prop} A B → A → B = coe in",
  "let trS : {A : Set}(B : A → Set){x y} → Eq x y → B x → B y",
  "    = λ {A} B {x}{y} p bx. coe (ap B p) bx in",
  "let trP : {A : Set}(B : A → Prop){x y} → Eq x y → B x → B y",
  "    = λ {A} B {x}{y} p bx. coe (ap B p) bx in",

  "let exfalsoS : {A : Set}  → ⊥ → A = exfalso in",
  "let exfalsoP : {A : Prop} → ⊥ → A = exfalso in",
  "let trans : {A : Set}{x y z : A} → Eq x y → Eq y z → Eq x z",
  "    = λ {_}{x} p q. trP (λ z. Eq x z) q p in",

  "let irrel1 : Eq (λ (f : Set → ⊤ → Set) (x : ⊤) (y : ⊤). f Set x)",
  "                (λ f x y. f Set y) = refl in",

  "let irrel2 : EqP (λ (x : ⊤)(y : ⊤). x) (λ x y. y) = reflP in",

  "Set"
  ]

test3 = main' "type" $ unlines [
  -- for testing proof irrelevance
  "let EqP    : {A : Prop} → A → A → Set = λ {A} x y. (P : A → Set) → P x → P y in",
  "let reflP  : {A x} → EqP {A} x x = λ P px. px in",

  -- "let coeS : {A B : Set}  → Eq A B → A → B = coe in",
  -- "let coeP : {A B : Prop} → Eq {Prop} A B → A → B = coe in",
  -- "let trS : {A : Set}(B : A → Set){x y} → Eq x y → B x → B y",
  -- "    = λ {A} B {x}{y} p bx. coe (ap B p) bx in",
  -- "let trP : {A : Set}(B : A → Prop){x y} → Eq x y → B x → B y",
  -- "    = λ {A} B {x}{y} p bx. coe (ap B p) bx in",

  -- "let exfalsoS : {A : Set}  → ⊥ → A = exfalso in",
  -- "let exfalsoP : {A : Prop} → ⊥ → A = exfalso in",
  -- "let trans : {A : Set}{x y z : A} → Eq x y → Eq y z → Eq x z",
  -- "    = λ {_}{x} p q. trP (λ z. Eq x z) q p in",

  -- "let irrel1 : Eq (λ (f : Set → ⊤ → Set) (x : ⊤) (y : ⊤). f Set x)",
  -- "                (λ f x y. f Set y) = refl in",

  -- "let irrel2 : EqP (λ (x : ⊤)(y : ⊤). x) (λ x y. y) = reflP in",

  -- "let foo : (A : Set) × (A → Set) = (Set, λ A. A) in",

  "((Set, λ (x:Set).x), (Set, tt))"
  ]
