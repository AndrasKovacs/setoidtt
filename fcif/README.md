## fcif

Implementation of the elaborator in the draft paper "Elaboration with
First-Class Implicit Function Types".

We also have here a small supplementary Agda file,
[TelescopeDerivation.agda](TelescopeDerivation), which contains a derivation
of telescopes and curried functions from Section 4 of the paper.

#### Installation

- Install Haskell Stack: https://docs.haskellstack.org/en/stable/README/ if you don't already have it
- `stack install` from this directory
- This copies the executable `fcif` to `~/.local/bin`.
- Agda installation for checking the Agda file: see [Agda
  docs](https://agda.readthedocs.io/en/v2.6.0.1/getting-started/installation.html). A
  standard library is also required.

#### Usage

The executable `fcif` reads an expression from standard input.

- `fcif elab` prints elaboration output.
- `fcif nf` prints normal form.
- `fcif type` prints the type of the expression.

See [benchmarks.fcif](benchmarks.fcif) here for an example file.
