# Reading guide

This guide lists every Lean module with the results of the manuscript that it
proves. Paths are relative to `FibonacciCriterion/`. Each module begins with a
header that describes its content and names its main declarations.
[PAPER_CORRESPONDENCE.md](PAPER_CORRESPONDENCE.md) lists the places where the
Lean proof argues differently from the manuscript.

## The main theorem

Read these modules first, in this order.

| Module | Content |
| --- | --- |
| `Forms.lean` | Positive-definite forms with integral Gram matrices |
| `Statement.lean` | The set `C` and the statements to prove |
| `Criterion/Sufficiency.lean` | Sufficiency of the criterion (§7) |
| `Criterion/Proof.lean` | The criterion from the classical results (Theorem 1.1) |
| `Criterion/Theorem.lean` | The Fibonacci criterion (Theorem 1.1) |
| `Example.lean` | An example: `x² + 2y² + 5z² + 5w²` |

`ClassicalInputs/Definitions.lean` states the classical results that
`Criterion/Proof.lean` takes as a hypothesis, and
`ClassicalInputs/Theorems.lean` proves them. A reader who accepts those
results needs, from `ClassicalInputs/`, only `Definitions.lean`,
`Representation.lean`, and the elementary reductions in `ThreeSquares/`, which
do not use the three-square theorem.

## §2 Fibonacci arithmetic

| Module | Content |
| --- | --- |
| `Fibonacci/Growth.lean` | Monotonicity of `Fₙ / n` (Lemma 2.1) |
| `Fibonacci/Period.lean` | Fibonacci residues from a return of the state |
| `Fibonacci/SmallModuli.lean` | Fibonacci numbers modulo 2, 3, 5, 8, and 16 |
| `Fibonacci/Addition.lean` | The Fibonacci addition formula over the integers |
| `Fibonacci/Twofold.lean` | Multiplying the Fibonacci index by 2 |
| `Fibonacci/Threefold.lean` | Multiplying the Fibonacci index by 3 |
| `Fibonacci/Fivefold.lean` | Multiplying the Fibonacci index by 5 |
| `Fibonacci/ValuationInputs.lean` | The Fibonacci valuation formulas and the bounds (1) |
| `Fibonacci/Valuations.lean` | Fibonacci valuations at 2, 3, and 5 (Lemma 2.2) |

## §3 Escalation through rank 3

| Module | Content |
| --- | --- |
| `Escalation/Pairing.lean` | The pairing and the binary escalators |
| `Escalation/BinaryOneOne.lean` | Escalation of `⟨1,1⟩` |
| `Escalation/NormTwoReduction.lean` | Reduction along a vector of norm 2 |
| `Escalation/BinaryOneTwoRank.lean` | The truant 5 of `⟨1,2⟩` raises the rank |
| `Escalation/BinaryOneTwo.lean` | Escalation of `⟨1,2⟩` |
| `Escalation/NineTernaryEscalators.lean` | The nine ternary escalators |
| `Escalation/NineTernaryFrames.lean` | Escalation to the nine ternary escalators (Proposition 3.1) |
| `Escalation/QuaternaryEscalation.lean` | Quaternary escalations inside an ambient form (Lemma 3.6) |
| `Escalation/TernaryTruants.lean` | The Fibonacci truants of the nine ternary escalators (Propositions 3.2 and 3.5) |

Propositions 3.2 and 3.3 are classical results; see the last section. The
results of §3 about the form `f` (Lemma 3.4, Proposition 3.5) are listed
under §6.

## §4 Extensions of the ternary escalators

| Module | Content |
| --- | --- |
| `Forms/TernaryGram.lean` | Symmetric ternary Gram matrices |
| `Forms/QuaternaryExtension.lean` | Quaternary extensions and their orthogonal sublattices (Lemmas 4.1 and 4.2) |

Lemma 4.3 is proven with Propositions 5.11 and 5.12 (`Regular/Escalator113.lean`,
`Regular/Escalator125.lean`), and Lemma 4.4 in `Irregular/EscalatorF.lean`.

## §5 Extensions of the regular ternaries

| Module | Content |
| --- | --- |
| `Regular/TwoAdicSubtraction.lean` | The 2-adic exceptional families and the subtraction table (Lemma 5.2 (ii)) |
| `Regular/TwoAdicEscalators.lean` | Ternaries with obstructions at 2 (Lemmas 5.2 and 5.4) |
| `Regular/TwoAdicFibonacci.lean` | Fibonacci members of the 2-adic families (Lemmas 2.4 and 5.3) |
| `Regular/TwoAdicExtensions.lean` | Extensions of the ternaries with obstructions at 2 (§5.1) |
| `Regular/TwoAdicUniversality.lean` | Fibonacci-universality in the 2-adic cases (Proposition 5.1) |
| `Regular/OddPrimeTools.lean` | Tools for obstructions at odd primes (Lemmas 5.8 and 5.10) |
| `Regular/Escalator113.lean` | Fibonacci-universality of extensions of `⟨1,1,3⟩` (Proposition 5.11) |
| `Regular/Escalator125.lean` | Fibonacci-universality of extensions of `⟨1,2,5⟩` (Proposition 5.12) |

## §6 Extensions of `f`

| Module | Content |
| --- | --- |
| `Irregular/Forms.lean` | The forms `f` and `h` and square transfers |
| `Irregular/Eligibility.lean` | Eligible integers not divisible by 49 |
| `Irregular/EligibilityResidues.lean` | Eligibility as a condition modulo 49 |
| `Irregular/EligibilitySquareFactors.lean` | Eligibility and square factors prime to 7 |
| `Irregular/Transfers.lean` | The square-transfer matrices (Table 3) |
| `Irregular/TransferPrimes.lean` | Primality of the transfer primes |
| `Irregular/ModTwelve.lean` | The modulo-12 transfer from `h` to `f` (Lemma 3.4) |
| `Irregular/Subtraction.lean` | Subtractions for `f ⊥ ⟨q⟩` (Lemmas 6.3, 6.4, and 6.5) |
| `Irregular/SevenUniversal.lean` | The universal form `f ⊥ ⟨7⟩` (Proposition 6.2) |
| `Irregular/InitialWindow.lean` | Fibonacci numbers represented by `f` below index 48 (Proposition 3.5) |
| `Irregular/RestrictedCover.lean` | The congruence cover (Lemma 6.6) |
| `Irregular/LargeIndices.lean` | Fibonacci numbers from index 48 for `f ⊥ ⟨q⟩` (Proposition 6.1) |
| `Irregular/EscalatorF.lean` | The irregular escalator `f` (Lemma 4.4, Proposition 6.1) |

## §7 The criterion and its minimality

| Module | Content |
| --- | --- |
| `Criterion/FourSquareExtension.lean` | The four-square extension (§7) |
| `Criterion/Truants.lean` | Fibonacci truants are indispensable (§7) |
| `Criterion/TableOne.lean` | The ten escalators of Table 1 |
| `Criterion/TableOneForms.lean` | The escalators of Table 1 as positive-definite forms |
| `Criterion/TableOneCongruences.lean` | The congruence checks of Table 1 |
| `Criterion/Indispensability.lean` | Minimality of the criterion (§7) |

`Criterion/Sufficiency.lean`, `Criterion/Proof.lean`, and
`Criterion/Theorem.lean` are listed in the first section.

## Elementary arithmetic

| Module | Content |
| --- | --- |
| `Arithmetic/PrimePowerNormalization.lean` | Factorizations by a power of a fixed base |
| `Arithmetic/QuadraticCongruence.lean` | A quadratic congruence over `𝔽_p` (Lemma 5.9) |
| `Arithmetic/RootLifting.lean` | Lifting a root of `q k² ≡ N` from `p` to `p²` |
| `Arithmetic/CenteredCRT.lean` | Centered Chinese remainders |

## Classical results

| Module | Content |
| --- | --- |
| `ClassicalInputs/Definitions.lean` | The classical results used by the proof |
| `ClassicalInputs/Representation.lean` | The classical representation theorems used by the proof |
| `ClassicalInputs/Theorems.lean` | Proofs of the classical results |
| `ClassicalInputs/Mordell.lean` | The Mordell construction |
| `ClassicalInputs/DeterminantSeven.lean` | Representation by `f` or `h` (Proposition 3.3) |

The three-square theorem and the forms that reduce to it (`⟨1,1,2⟩`,
`⟨1,2,2⟩`, `⟨1,2,4⟩`; the reduction for `g` is in
`ClassicalInputs/Representation.lean`):

| Module | Content |
| --- | --- |
| `ClassicalInputs/ThreeSquares/Reductions.lean` | Three squares and `⟨1,1,2⟩` |
| `ClassicalInputs/ThreeSquares/DiagonalReductions.lean` | The forms `⟨1,2,2⟩` and `⟨1,2,4⟩` |
| `ClassicalInputs/ThreeSquares/Scaling.lean` | Scaling and descent by 4 for three squares |
| `ClassicalInputs/ThreeSquares/Obstruction.lean` | The three-square obstruction |
| `ClassicalInputs/ThreeSquares/Theorem.lean` | The Gauss–Legendre three-square theorem |

The criteria of Proposition 3.2 for `⟨1,1,3⟩`, `⟨1,2,3⟩`, and `⟨1,2,5⟩`:

| Module | Content |
| --- | --- |
| `ClassicalInputs/Regular113/Obstruction.lean` | The obstruction for `⟨1,1,3⟩` |
| `ClassicalInputs/Regular113/ResidueRows.lean` | Residue tables for the `⟨1,1,3⟩` Mordell construction |
| `ClassicalInputs/Regular113/Mordell.lean` | Sufficiency for `⟨1,1,3⟩`: the Mordell construction |
| `ClassicalInputs/Regular113/Classification.lean` | The determinant-3 classification and the criterion for `⟨1,1,3⟩` |
| `ClassicalInputs/Regular123/Obstruction.lean` | The obstruction for `⟨1,2,3⟩` |
| `ClassicalInputs/Regular123/SquareRoots.lean` | Square roots for the `⟨1,2,3⟩` Mordell construction |
| `ClassicalInputs/Regular123/Mordell.lean` | Sufficiency for `⟨1,2,3⟩`: the Mordell construction |
| `ClassicalInputs/Regular123/Classification.lean` | The determinant-6 classification and the criterion for `⟨1,2,3⟩` |
| `ClassicalInputs/Regular125/Obstruction.lean` | The obstruction for `⟨1,2,5⟩` |
| `ClassicalInputs/Regular125/Mordell.lean` | Sufficiency for `⟨1,2,5⟩`: the Mordell construction |
| `ClassicalInputs/Regular125/Classification.lean` | The determinant-10 classification and the criterion for `⟨1,2,5⟩` |

Minkowski reduction and the lists of reduced ternary Gram matrices:

| Module | Content |
| --- | --- |
| `ClassicalInputs/Reduction/Lattice.lean` | Ternary Gram matrices as TauCeti lattices |
| `ClassicalInputs/Reduction/Bounds.lean` | Integer inequalities for Mahler's bound |
| `ClassicalInputs/Reduction/ReducedGram.lean` | Minkowski-reduced ternary Gram matrices |
| `ClassicalInputs/Reduction/Classification.lean` | Finite classification of reduced ternary Gram matrices |

Proposition 3.3:

| Module | Content |
| --- | --- |
| `ClassicalInputs/DeterminantSeven/ReducedMatrices.lean` | The reduced Gram matrices of determinant 7 |
| `ClassicalInputs/DeterminantSeven/Classes.lean` | The reduced Gram matrices in the classes of `f` and `h` |
| `ClassicalInputs/DeterminantSeven/ZeroCount.lean` | The number of zeros modulo 7 |
| `ClassicalInputs/DeterminantSeven/BasisChange.lean` | Changes of basis and reduction modulo 7 |
| `ClassicalInputs/DeterminantSeven/GramMatrices.lean` | Representation by `f` or `h`: the Gram matrices (Proposition 3.3) |
| `ClassicalInputs/DeterminantSeven/Unramified.lean` | Representation by `f` or `h`: the unramified case `7 ∤ n` (Proposition 3.3) |
| `ClassicalInputs/DeterminantSeven/Ramified.lean` | Representation by `f` or `h`: the ramified case `n = 7u` (Proposition 3.3) |
