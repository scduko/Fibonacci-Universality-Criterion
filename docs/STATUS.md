# Verification status

## What is proven

The main theorem, in `FibonacciCriterion/Criterion/Theorem.lean`, is

```lean
theorem fibonacci_criterion :
    (∀ {ι : Type} [Fintype ι] (Q : Form ι),
        FibonacciUniversal Q ↔ ∀ t ∈ criterion, Q.Represents t) ∧
      (∀ S : Set ℕ, IsFibonacciCriterionSet S →
        (criterion : Set ℕ) ⊆ S) ∧
      IsMinimalFibonacciCriterionSet (criterion : Set ℕ) ∧
      ∀ S : Set ℕ, IsMinimalFibonacciCriterionSet S →
        S = (criterion : Set ℕ)
```

where `criterion = {1, 2, 3, 5, 21, 55, 610, 987, 832040, 267914296}`. A form
of any finite rank represents every Fibonacci number if and only if it
represents every element of `criterion`; every Fibonacci criterion set
contains `criterion`; and `criterion` is the unique minimal one. `Form` and
`FibonacciUniversal` are defined in `FibonacciCriterion/Forms.lean`, and
`criterion`, `IsFibonacciCriterionSet`, and `IsMinimalFibonacciCriterionSet`
in `FibonacciCriterion/Statement.lean`.

The theorem has no hypotheses. In particular, the classical results that the
proof uses (the three-square theorem, the criteria of Proposition 3.2, the
sufficiency direction of Proposition 3.3, and the valuation formulas of
Lemma 2.2) are proven in
`FibonacciCriterion/ClassicalInputs/` or in the pinned dependencies.

`fibonacci_criterion_matrix`, in the same file, states the equivalence for an
integer matrix that is positive definite in the sense of Mathlib's
`Matrix.PosDef`, so the statement can be read without the definitions of this
repository.

## How it is checked

The workflow `.github/workflows/lean.yml` runs on every pull request and on
every push to `main`, and it can be started by hand. GitHub skips a pull
request or push when every file it changes is a Markdown file or lies under
`docs/` or `paper/`. A run performs four checks and fails unless all four
pass.

1. **Build.** `lake build` compiles the root module `FibonacciCriterion` and
   the modules it imports, which are all 90 modules of the library, with
   warnings treated as errors.
2. **Lint.** `lake lint` runs the Batteries linter on every declaration of
   those modules.
3. **Kernel replay.** `lake env leanchecker -v FibonacciCriterion` takes
   every compiled module whose name begins with `FibonacciCriterion` and has
   the Lean kernel check its declarations again, independently of the
   elaborator that produced the proofs.
4. **Axiom audit.** `axiom-audit` loads the root module and examines every
   declaration defined in those modules. None may depend on an axiom other
   than `propext`, `Classical.choice`, and `Quot.sound`. The log of a run
   states how many declarations were audited.

The workflow pins the actions it uses by commit. The pinned `lean-action`
runs the four checks in the order above; for the audit it fetches
[axiom-audit](https://github.com/leanprover-community/axiom-audit) at tag
`v0.1.2` and verifies its commit before building it.

The axiom audit is what excludes `sorry`, `admit`, added axioms, and
`native_decide`: each would appear as an axiom outside the allowlist. The
finite computations are propositions proven by `decide` or `decide +kernel`,
which the kernel evaluates, so they add no trust beyond the kernel. Some of
them raise `maxRecDepth` or remove the heartbeat limit (`set_option`); these
options affect elaboration only, not what the kernel accepts.
[PAPER_CORRESPONDENCE.md](PAPER_CORRESPONDENCE.md) lists the checks.

One statement in this file is not checked by the workflow. Every declaration
is used by the main theorems or by the example in `Example.lean`, with four
exceptions: `fib_convention`, which records the indexing of the Fibonacci
numbers; `irregularCoefficients_length`, which records the count 82 of
Lemma 4.4; `Form.posDef_gram`, which states that the Gram matrix of a `Form`
is positive definite in Mathlib's sense; and the `simp` lemma
`Form.ofPosDef_gram`. This was established by a dependency scan run by hand
when the file was last revised.

## Versions

- Lean 4.35.0 (`lean-toolchain`).
- Mathlib, atlas-lean, and TauCeti at the commits pinned in
  `lake-manifest.json`.
- The section "Lean formalization" of the manuscript describes this
  repository.

## Reproducing the checks

These commands run the four checks from the root of a fresh checkout. They
need `git` and [elan](https://lean-lang.org/install/), which installs the
Lean version named in `lean-toolchain`.

```sh
# Dependencies: Lake fetches the revisions pinned in lake-manifest.json, and
# Mathlib's cache tool downloads Mathlib's compiled files.
lake exe cache get

# Build all 90 modules.
lake build

# Linter.
lake lint

# Kernel replay, one module at a time as in the workflow.
LEAN_NUM_THREADS=1 lake env leanchecker -v FibonacciCriterion

# Axiom audit, with the tool at the version that the workflow uses.
git clone --depth 1 --branch v0.1.2 \
  https://github.com/leanprover-community/axiom-audit.git ../axiom-audit
if [ "$(git -C ../axiom-audit rev-parse HEAD)" != \
     "46024e005996495c65ef609368e11ab39c4222e3" ]; then
  echo "Unexpected axiom-audit version" >&2
  exit 1
fi
cp lean-toolchain ../axiom-audit/
(cd ../axiom-audit && lake build)
lake env ../axiom-audit/.lake/build/bin/axiom-audit \
  --allow propext,Classical.choice,Quot.sound --root FibonacciCriterion
```

Each command exits with status 0 on success. The linter ends with "Linting
passed for FibonacciCriterion", and the audit with the number of declarations
audited and "all within the allowlist".

The workflow sets `LEAN_NUM_THREADS=1` for the whole job. Only the replay
needs it: with one thread `leanchecker` replays the modules one after another
and used about 7 GB of memory when these commands were tested. Without the
variable it replays them in parallel and needs considerably more: 15 GB was
not enough on a machine with four cores.
