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
  let elab :: IO (Tm, Tm, Tm)
      elab = do
        reset
        (t, src) <- getTm
        (t, a, au) <- inferTopLams emptyCxt t `catch` displayError src
        t <- pure $ zonk VNil t
        let ~nt = quote 0 $ eval VNil t
        let ~na = quote 0 a
        pure (t, nt, na)

  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, nt, na) <- elab
      putStrLn $ show nt
    ["type"] -> do
      (t, nt, na) <- elab
      putStrLn $ show na
    ["elab"] -> do
      (t, nt, na) <- elab
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

-- does not work bc we only keep track of universe in unif
test2 = main' "elab" $ unlines [
  "let Eq : {A : Set} → A → A → Set = λ {A} x y. (P : _ → Set) → P x → P y in",
  "let refl : {A x} → Eq {A} x x = λ P px. px in",
  "let p1 : Eq {⊤ → ⊤ → ⊤}(λ (x : ⊤)(y : ⊤). x) (λ x y. y) = refl in",
  "Set"
  ]

-- works
test3 = main' "elab" $ unlines [
  "let Eq : {A : Prop} → A → A → Set = λ x y. (P : _ → Set) → P x → P y in",
  "let refl : {A x} → Eq {A} x x = λ P px. px in",
  "let p1 : Eq (λ (x : ⊤)(y : ⊤). x) (λ x y. y) = refl in",
  "Set"
  ]
