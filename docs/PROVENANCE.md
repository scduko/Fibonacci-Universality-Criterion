# Sources

## The manuscript

Scott Duke Kominers, *A Fibonacci Analogue of the Fifteen Theorem*. The
numbering of results, tables, and equations in this repository follows the
manuscript; its section "Lean formalization" describes this formalization.

The four-square extension of §7 follows the extension principle of
Kala–Krásenský–Romeo and the construction of Kim–Lee–Oh, as the manuscript
does.

## Explicit data

Every table in the Lean source is checked by the kernel, so none of it has to
be trusted. The data come from the following places.

- **Transfer matrices** (`Irregular/Transfers.lean`). The twelve integral
  matrices of Table 3: the maps for 2 and 3 used in Lemma 3.4 and the maps for
  the ten primes of `P₇`, as printed in the manuscript. Each identity
  `f(B_p v) = p² h(v)` is checked by `ring`, and
  `Irregular/TransferPrimes.lean` checks that each `p` is a prime other
  than 7.
- **Table 1** (`Criterion/TableOne.lean`). The ten forms `P_t` with their
  truants, indices, and congruence data, as in the manuscript.
  `Criterion/TableOneCongruences.lean` proves that each congruence excludes
  the truant for all integer coordinates. The representations of the smaller
  Fibonacci numbers are not tabulated: `Criterion/Indispensability.lean`
  gives explicit vectors up to rank 2 and uses the truant column of Figure 1
  (`Escalation/TernaryTruants.lean`) for the six ternary forms.
- **Proposition 3.5** (`Irregular/InitialWindow.lean`). The representations
  of `F₀, …, F₇` by `f` and the six vectors for the indices 9, 10, 15, 33,
  34, and 39, as in the manuscript. At every other index from 9 to 47, a
  kernel check shows that `Fₙ` is eligible and is not 7 or 10 modulo 12, so
  Proposition 3.3 and Lemma 3.4 apply.
- **Lemma 6.6** (`Irregular/RestrictedCover.lean`). The eight groups of
  values of `q` and their primes, as in the manuscript. For each group, a
  checker follows the Fibonacci recurrence modulo 12 and the group's primes
  through one return time. At each index class it checks that the residue
  pair is outside (7) or that some prime `p` of the group has a nonzero `k`
  with `q k² ≡ Fₙ (mod p)`, and at the end it checks that the state has
  returned to `(0, 1)`. Lean proves the checker sound, so the return times are
  verified, not assumed.
- **The small-prime table** for the indices 57 and 58
  (`Irregular/LargeIndices.lean`), with one row for each index and
  value of `q`. Each row is checked together with the bound of Lemma 6.5.
- **The table of `v₂(Fₙ)` and `u₂(Fₙ)`** for `n ≤ 64`
  (`Regular/TwoAdicFibonacci.lean`), used for Lemmas 2.4 and 5.3.
- **Reduced ternary Gram matrices** of determinants 3, 6, 7, and 10
  (`ClassicalInputs/Reduction/Classification.lean` and the files that use
  it). The lists are confirmed by a kernel search over the box of reduced
  matrices.

## Classical results

The criteria for `⟨1,1,3⟩`, `⟨1,2,3⟩`, and `⟨1,2,5⟩` are proven by the
Mordell-type construction of Blackwell, Durham, Thompson, and Treece. For
even inputs at `⟨1,2,5⟩` the parameters are chosen so that the form represents
an odd integer; see `ClassicalInputs/Regular125/Mordell.lean`. The manuscript
cites Jones–Pall for these criteria; see
[PAPER_CORRESPONDENCE.md](PAPER_CORRESPONDENCE.md).

## Dependencies

- Lean 4.35.0 (`lean-toolchain`).
- Mathlib, at the commit pinned in `lake-manifest.json`. It supplies, among
  other results, Lagrange's four-square theorem (`Nat.sum_four_squares`),
  Dirichlet's theorem on primes in arithmetic progressions, and quadratic
  reciprocity.
- [atlas-lean](https://github.com/facebookresearch/atlas-lean), for the
  three-square theorem of Gauss and Legendre.
- [TauCeti](https://github.com/TauCetiProject/TauCeti), for Minkowski
  reduction of positive-definite lattices.
