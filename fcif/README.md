## fcif

Implementation of the draft paper "Elaboration with First-Class Implicit
Function Types".

#### Installation

- Install Haskell Stack: https://docs.haskellstack.org/en/stable/README/ if you don't already have it
- `stack install` from this directory
- This copies the executable `fcif` to `~/.local/bin`.

#### Usage

The executable `fcif` reads an expression from standard input.

- `fcif elab` prints elaboration output.
- `fcif nf` prints normal form.
- `fcif type` prints the type of the expression.

See [benchmark.fcif](benchmark.fcif) here for an example file.
