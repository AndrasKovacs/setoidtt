# setoidtt-proto
Prototype implementation for a variant of setoid type theory. This repository currently contains a stack package in [proto](proto), whose source code is forked from [fcif](https://github.com/AndrasKovacs/icfp20sub/tree/master/fcif).

The goal of the current `setoidtt` is to figure out various details in design choices, type inference, evaluation and ergonomics. Thus it lacks many features and it only operates on a file containing a single expression. Its pretty printing and error messages are also very rough.

I plan to start a second "production-strength" implementation after basic design choices are hammered out. The second version will hopefully turn into a longer-term project where I throw in all kinds of advanced elaboration features. 

#### Features & inspiration

Precedents:

- [Observational Type Theory](https://www.researchgate.net/publication/248136193_Towards_Observational_Type_Theory), which is
  approximately implemented in [sott](https://github.com/bobatkey/sott).
- [Setoid type theory](https://hal.inria.fr/hal-02281225/document).

The current implementation differs from both of the above. However, my intended semantics is clearly in setoids, i.e. every closed type is a set together with a proof-irrelevant equivalence relation, and every dependent type is a setoid fibration. I also find "setoid" more precise than "observational", since the latter is perhaps also descriptive of homotopy type theories, and we explicitly disallow types above the h-level of sets.

Core theory:

- Strict `Prop` with [definitional proof irrelevance](https://dl.acm.org/doi/10.1145/3290316).
- A universe `Set` of set(oid)s with `Prop : Set` and `Set : Set`.
- `Prop` is *not* a subtype of `Set`. An embedding from `Prop` to `Set` is definable though, with sigmas and equality.
- Sigma, Pi, `⊤` and `⊥` type formers. `⊤` and `⊥` are in `Prop`. Sigma is in `Prop` if both fields are in `Prop`, Pi is in `Prop` if the codomain is in `Prop`. We can eliminate from `⊥` to both `Prop` and `Set`.
- Equality type `Eq : {A : Set} → A → A → Prop`. 
- `coe : {A B : Set} → Eq A B → A → B`.
- `refl : {A : Set}{x : A} → Eq x x`.
- `ap : {A B : Set}(f : A → B){x y : A} → Eq x y → Eq (f x) (f y)`.
- `Eq` and `coe` computes on type structure, in particular we have
  - Propositional extensionality: `Eq {Prop} A B = ((A → B) ∧ (B → A))`
  - Function extensionality: `Eq {(x : A) → B} f g = ((x : A) → Eq (f x) (g x))`.
  - Injective type formers.
  - Besides the canonical cases for `coe` computation, we also have `coe (p : Eq A A) x = x` and `coe p (coe q x) = coe (trans q p) x`. Semantically, these correspond to open types being split fibrations, not just fibrations.

That's it. In the actual implementation, a few additional convenient primitives are built in, which are nevertheless derivable in the above core theory:

- `coe` for `Prop`, an overloading of `coe` as `Eq {Prop} A B → A → B`.
- Symmetry and transitivity for `Eq`.

Implementation features:

- Implicit arguments, first-class implicit function types, metavariables, pattern unification with pruning.
- Universe inference with simple but apparently effective universe unification, for universe polymorphic constructions
  such as functions, sigmas and `coe`.
- Enhanced type inference for `Eq` and `coe`: extension of bidirectional discipline to also propagate information about equation sides + a variant of glued evaluation which tracks `Eq` types even after they are computed away.
- Type-based field projections for right-nested sigma types. E.g. if `t : (A : Set) × (foo : A) × ⊤`, then
  `t.foo : t.A`.
- A novel solution for unification with strict `Prop`, where unification is universe-directed but not type-directed. I find this a sweet spot between the full-blown type directed unification of Agda (which is powerful but adds complexity and performance overhead), and the fully syntax-directed unification of Coq, which is frankly rather ugly and fiddly for strict `Prop`.

Difference from prior/related works:

1. Versus OTT: no heterogeneous equality. I think that HEq is an unnecessary complication with dubious practical benefits. The entire point of using HEq in usual MLTT+UIP is that we want to avoid proving and invoking coercion computation laws as much as possible, instead collecting every coercion into a single hidden coercion, which can be eliminated by UIP in one shot when we want to go back to homogeneous equality. Given computing coercion and proof-irrelevant equalities, the motivation for HEq is largely lost. While we can still try to base our system around HEq, as OTT did, we actually end up with more proof obligations and code duplication in general, as HEq-s require re-proving type equalities whenever we want to talk about value equalities.

2. Versus STT: no explicit substitutions, no "dependent" equality. The point here is that as soon as we have every type in some universe, type equality is *always* just equality of type codes, and coercion is always just over a single homogeneous equality of type codes. Hence, the "local universes"-style coercions with explicit substitutions are not necessary anymore, which is a good news, since the STT-style coercion would be a major pain to implement in an ergonomic way.

3. Versus [XTT](https://arxiv.org/abs/1904.08562): XTT is a set-truncated cubical type theory. Compared to it, `setoidtt` is simpler in syntax and semantics, supports more computation rules (e.g. function equality is pointwise by definition) and supports propositional extensionality. `setoidtt` also has no need for the rather ugly typecasing construction in XTT. IMO, cubical type theory is oversized for set-level mathematics, and `setoidtt` seems to be practically better in this setting.

Semantics: TODO, but I conjecture that a standard setoid model can be given similarly to STT (of course, assuming we have consistent universe setup without `Set : Set`). In the current system, the only dubious point is the strict computation of `Eq` on canonical type formers. This is semantically justified by a very general, hitherto undescribed form of induction-recursion. If injectivity of type formers is only given weakly as "projections", as in [sott](https://github.com/bobatkey/sott), that can be modeled with large induction-induction, see "Constructing a universe for the setoid model" [here](https://types2020.di.unito.it/abstracts/BookOfAbstractsTYPES2020.pdf).

AFAIK, the interpretation of split fibration laws for general inductive types is also open research topic now, but we don't yet have such types here.

#### Installation

- Install Haskell Stack: https://docs.haskellstack.org/en/stable/README/ if you don't already have it
- `stack install` from this directory
- This copies the executable `setoidtt` to `~/.local/bin`.

#### Usage

The executable `setoidtt` reads an expression from standard input.

- `setoidtt elab` prints elaboration output.
- `setoidtt nf` prints the normal form of the input.
- `setoidtt type` prints the normal form of the type of the input.
