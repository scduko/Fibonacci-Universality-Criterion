# Correspondence with the manuscript

This file records every place where the Lean proof argues differently from
the manuscript (*A Fibonacci Analogue of the Fifteen Theorem*).
Where a result is not listed, the Lean proof follows the manuscript's
argument. The section "Lean formalization" of the manuscript summarizes the
main differences. "Stronger" and "weaker" compare the Lean statement with the
manuscript's statement of the same result.

Neither proof uses an external computational certificate. The Lean proof
contains finite checks that the manuscript does by hand or by short
calculation; each is a Lean statement with a proven soundness lemma, evaluated
by the kernel (`decide` or `decide +kernel`). They are listed at the end.

## Setting and main theorem

- **Forms, not lattices.** Lean works with positive-definite forms given by
  integral symmetric Gram matrices on an arbitrary finite index type
  (`Forms.lean`). It never builds the lattices `L_i` as submodules, and it
  has no general notion of truant or escalator. The escalation instead
  produces a *frame*: vectors `e₁, e₂, e₃` of the ambient form with the Gram
  matrix of one of the nine ternaries (`exists_nine_ternary_frame` in
  `Escalation/NineTernaryFrames.lean`; the predicate is `Form.IsFrame` in
  `Escalation/QuaternaryEscalation.lean`), and a vector `u` of truant norm.
- **Quaternary extensions.** The frame and `u` give the extension `L₄ = T + ℤu`
  of §§4 and 7, recorded by its Gram data `c` and `m` (the structure
  `QuaternaryExtension` in `Forms/QuaternaryExtension.lean`; `Form.extension`
  in `Escalation/QuaternaryEscalation.lean`); every value of `L₄` is
  a value of the ambient form. Propositions 5.1, 5.11, 5.12, and 6.1 are stated
  for quaternary extensions, as in the manuscript, and `Criterion.Sufficiency`
  assembles them as in §7. Positive definiteness of a ternary `T` and of an
  extension is stated at integral vectors (`TernaryGram.PosDef`,
  `QuaternaryExtension.PosDef`).
- **Theorem 1.1** is `fibonacci_criterion`
  (`Criterion/Theorem.lean`). `CriterionIndispensability` drops the
  finiteness of the criterion set and allows the value `0 = F₀`, so it is
  formally stronger. Uniqueness of the minimal set is proven directly. The
  general results of Kim–Kim–Oh and Kim–Lee–Oh cited in §1 are not
  formalized. The Fibonacci numbers are Mathlib's `Nat.fib`, with `F₀ = 0`
  and `F₁ = 1` (`fib_convention`); `FibonacciUniversal` includes `F₀ = 0`,
  which every form represents. That the two descriptions of `C` in the
  theorem agree, `{Fₙ : n ∈ {1, 3, 4, 5, 8, 10, 15, 16, 30, 42}} = C` as
  sets, is `fib_criterionIndices` (`Statement.lean`).
- **Corollary 1.2** is `fibonacciUniversal_of_represents_fib_le_42` and
  `not_isFibonacciCriterion_fib_le_41` (`Criterion/Theorem.lean`), by
  the manuscript's argument: `⟨1,1,2⟩` represents `F₀, …, F₄₁` and omits
  `F₄₂` (`truant_column`). The second statement says that representing
  `F₀, …, F₄₁` does not force Fibonacci-universality; it does not name the
  form.
- **Mathlib's definitions.** `Form` is defined in this repository.
  `Form.posDef_gram` and `Form.ofPosDef` relate it to `Matrix.PosDef`, and
  `fibonacci_criterion_matrix` states the equivalence of Theorem 1.1 for an
  integer matrix that is positive definite in that sense. `Example.lean`
  applies the theorem to `x² + 2y² + 5z² + 5w²`; the manuscript has no such
  example.

## §2 Fibonacci arithmetic

- **Lemma 2.1** (monotonicity of `Fₙ/n`) is `fib_succ_mul_gt`, for
  consecutive indices (`Fibonacci/Growth.lean`). Lemma 5.3 and Propositions
  5.11 and 5.12 use its consequence `fib_mul_le_of_le`.
- **Ranks of apparition** are not used in general. Lean proves the specific
  divisibility statements it needs, for the moduli 2, 3, 4, 5, 8, 9, and 16, by
  periodicity (`Fibonacci/SmallModuli.lean`, `Fibonacci/Twofold.lean`,
  `Fibonacci/Threefold.lean`).
- **Lemma 2.2** (valuations at 2, 3, 5) is proven, not cited
  (`Fibonacci/Valuations.lean`, assembled as `fibonacciValuationInputs`):
  - the proof uses the identities for `F₂ₘ`, `F₃ₘ`, and `F₅ₘ` with
    periodic base cases;
  - it does not use Lucas numbers;
  - only the step multiplying the index by `p` is proven, not the general
    lifting formula.

  The bounds (1) are `two_prime_power_bound`, `three_prime_power_bound`, and
  `five_prime_power_bound` (`Fibonacci/ValuationInputs.lean`).
- **Lemma 2.3.** Lean proves return times (`FibStateReturns`), never that a
  period is the least one. Of the six moduli in the lemma's table, it states
  the return times 20, 12, and 24 modulo 5, 8, and 16; `π(7)`, `π(12)`, and
  `π(49)` are not stated. Modulo 12 the proof uses the return times of the
  groups of Lemma 6.6, and modulo 7 and 49 it checks the Fibonacci numbers of
  Proposition 3.5 directly. The unit-residue remark that follows is not used.
- **Lemma 2.4.**
  - The 2-adic rows come from a kernel-checked table of `v₂(Fₙ)` and `u₂(Fₙ)`
    for `n ≤ 64` (`Regular/TwoAdicFibonacci.lean`), not from the valuation
    formula. The same table gives the later members used in Lemma 5.3.
  - The 3- and 5-adic rows (`obstructed_index` in `Regular/Escalator113.lean`
    and `Regular/Escalator125.lean`): a member has index divisible by 4 or 5,
    by `three_dvd_fib_iff` and `five_dvd_fib_iff` (periodicity,
    `Fibonacci/SmallModuli.lean`) rather than by Lemma 2.2, and the explicit
    factorizations of `F₄, F₈, F₁₂` and `F₅, F₁₀` exclude the earlier indices.
  - Membership of the truants is stated where it is used, as
    `TwoAdic.exceptional55`, `exceptionalF42`, `exceptionalF30`, and the
    nonsquare units `329` and `122` (`truant_not_square`). The 7-adic row is
    replaced by the displayed vectors for `F₁, …, F₇` and the modulo-49 row
    of Table 1.

## §3 Escalation through rank 3

- **Proposition 3.1** is proven in the direction the criterion uses: every
  form representing 1, 2, 3, 5 contains a frame with one of the nine Gram
  matrices (`exists_nine_ternary_frame`), by the manuscript's reductions.
  The converse (each of the nine occurs) and the determinants, hence
  inequivalence, are not stated; the criterion does not need them.
  - The cases `b = 1, m ∈ {2, 3}` (in Lean's parameters `e = 1`,
    `d ∈ {2, 3}`) are excluded by a congruence modulo 4 on the actual
    representation of 5.
  - The rational descents for the binary escalators are replaced by integral
    nonvanishing of a remainder vector (`Escalation/BinaryOneOne.lean`,
    `Escalation/BinaryOneTwoRank.lean`).
- **Proposition 3.2** (regular ternaries). Lean proves the integral criteria
  `Represents ↔ ¬ Exceptional` for every `n ≥ 0`: for `⟨1,1,1⟩`, `⟨1,1,3⟩`,
  `⟨1,2,3⟩`, `⟨1,2,5⟩` as the fields of `ClassicalRepresentation.Inputs`, and
  for `⟨1,2,2⟩`, `g`, `⟨1,1,2⟩`, `⟨1,2,4⟩` as consequences
  (`TwoAdic.represents122_iff`, `TwoAdic.representsG_iff`,
  `TwoAdic.represents112_iff`, `TwoAdic.represents124_iff`).
  - Regularity, the local-global statement, is not formalized. Every
    obstruction is proven as integral non-representation, not as a local
    obstruction over `ℤ_p`.
  - `⟨1,1,1⟩`: sufficiency comes from atlas-lean's three-square theorem.
  - `⟨1,2,2⟩`, `g`, `⟨1,1,2⟩`, `⟨1,2,4⟩` use the manuscript's identities.
  - `⟨1,2,3⟩`: the obstruction follows the manuscript's descent; the
    substitution `X = (x + 3z)/2`, `Z = (x - z)/2` and the halving are combined
    into one step.
  - `⟨1,1,3⟩`: the obstruction shows that `9 ∣ n` forces every coordinate to be
    divisible by 3, then excludes the class 6 modulo 9.
  - `⟨1,2,5⟩`: the obstruction follows the anisotropic-binary descent.
- **Sufficiency for `⟨1,1,3⟩`, `⟨1,2,3⟩`, `⟨1,2,5⟩`.** The manuscript cites
  Jones–Pall. Lean proves these criteria by the Mordell-type construction of
  Blackwell–Durham–Thompson–Treece:
  - primes in explicit progressions, from Dirichlet's theorem, and Jacobi
    reciprocity produce a positive-definite ternary form of determinant 3, 6,
    or 10 that represents the input
    (`ClassicalInputs/Mordell.lean`, `ClassicalInputs/Regular113/Mordell.lean`,
    `ClassicalInputs/Regular123/Mordell.lean`,
    `ClassicalInputs/Regular125/Mordell.lean`);
  - TauCeti's Minkowski reduction and kernel-checked lists of reduced matrices
    classify those forms up to the integers they represent: two classes at
    determinant 3, three at determinant 6, and four at determinant 10,
    including even-valued classes;
  - separating residues isolate the target: a value `≡ 5 (mod 8)`; an odd
    value `≡ 3 (mod 9)`; a value `≡ 6 (mod 16)` together with an odd value;
  - the factors 4 and 9 for `⟨1,1,3⟩`, 4 for `⟨1,2,3⟩`, and 4 and 25 for
    `⟨1,2,5⟩` are removed by induction.

  At determinant 10 one of the four classes is even-valued, so Lean requires
  the Mordell form to represent an odd integer. For odd inputs the input itself
  is odd. For even inputs, a Mordell form with `B = 0`, odd `a`, and leading
  coefficient `≡ 6 (mod 16)` represents only even integers (example at `m = 2`
  in the docstring of `Mordell125.NormalizedParameterConstruction`), so Lean
  takes other parameters for `m = 2n`: `a = 4q` for `n ≡ 1 (mod 4)`, and
  `B = 1` or `B = 5` for `n ≡ 3 (mod 4)`.
- **The truant column** of Figure 1 (Propositions 3.2 and 3.5) is
  `truant_column` (`Escalation/TernaryTruants.lean`), for all nine ternary
  escalators: each represents every Fibonacci number before its truant, by the
  criteria of Proposition 3.2 and Lemma 2.4 (displayed vectors for `f`), and
  omits the truant (Lemma 3.6 with `k = 1`). Minimality uses it for the six
  ternary escalators of Table 1, and Corollary 1.2 for `⟨1,1,2⟩`.
- **Proposition 3.3** is formalized as its sufficiency direction for positive
  integers not divisible by 49: `ResidualEligible n` implies that `f` or `h`
  represents `n` (`DeterminantSevenGenus.eligible_f_or_h`). Of its
  applications, only Proposition 6.2 meets multiples of 49, and its induction
  scales a representation by `f ⊥ ⟨7⟩` by 7. Of the necessity direction, only
  the 7-adic obstruction of `f` is formalized: `f` omits `7^{2a+1} u` with `u`
  a nonsquare modulo 7 (`EscalatorF.not_representsF_obstructed`). Its descent
  runs on `2f = 2x² + (2y+z)² + 7z²`; the manuscript uses
  `f ≡ x² + 2(y + 4z)² (mod 7)`. In the proof of sufficiency:
  - **Mahler's bound** `abc ≤ 2·det` is proven, not cited
    (`ClassicalInputs/Reduction/Bounds.lean` for the integer inequality,
    `product_le_two_mul_determinant` in
    `ClassicalInputs/Reduction/ReducedGram.lean`), from TauCeti's
    Minkowski-reduced bases.
  - **The list of reduced matrices** is confirmed by a kernel search over 5,040
    tuples, giving the fifteen reduced matrices.
  - **The invariant separating the classes** is the number of zeros modulo 7: 7
    for `f` and `h`, 91 for the third class
    (`ClassicalInputs/DeterminantSeven/ZeroCount.lean`; Lean checks only that
    a listed matrix with seven zeros lies in the classes of `f` and `h`). The manuscript uses
    the square class of the determinant of the binary quotient instead. The
    twelve matrices of the third class are excluded by this count; they are
    never shown to be equivalent to `K₇`.
  - **Transport of the count** across a change of basis reduces the integral
    change-of-basis matrix modulo 7
    (`ClassicalInputs/DeterminantSeven/BasisChange.lean`).
  - **The unramified construction** (`7 ∤ n`) uses the manuscript's
    congruences:
    - `(n/q) = 1`, for the auxiliary prime `q` (the manuscript's `ℓ`), is
      proven by stripping factors of 2 and applying Jacobi reciprocity;
    - positivity is an explicit `LDLᵀ` identity;
    - the zero count 7 is checked over all residues `(n, a, L, c)` modulo 7
      with `na ≡ 2` and `c ≡ aL²`; the manuscript reads the square class off
      the leading binary minor `ℓ ≡ 1`.
  - **The ramified construction** (`n = 7u`) uses the progression
    `p ≡ −7 (mod 8u)` with `p > 8u` (the manuscript has `ℓ > 7u`), and computes
    `(−u/p)` from `u = 2^e·v` and a table of `v` modulo 28 rather than from
    `(m/7)`. The manuscript's congruence `a₀c₀ ≡ u⁻¹ (mod 7)` becomes a check
    over residues that `ac` is a nonzero square, followed by the zero count
    over the residues `(a, c)`.
  - **The remarks** that 7 is locally represented by `f` and that `f` is
    irregular are not formalized. That `f` omits 7 is proven by bounded
    enumeration.
- **Lemma 3.4** (`Irregular/ModTwelve.lean`) uses the manuscript's maps `B₂/2`
  and `B₃/3`; the parity and sign choice is checked over `(ℤ/6)³`.
- **Proposition 3.5** (`representsF_fib_initial`) covers `n < 48`, `n ≠ 8`,
  including `n = 0`. Two kernel checks verify the fourteen vectors of
  `initialWitnesses`, for `F₀, …, F₇` and for the six indices 9, 10, 15, 33,
  34, 39 (`initialWitnesses_checked`), and, at every other index from 9 to 47,
  the eligibility and the residue modulo 12 (`initial_window_checked`). That
  `F₄₈` is the next exception is not stated. It would follow from
  `EscalatorF.not_representsF_obstructed` with `a = 0`, since
  `F₄₈ ≡ 21 (mod 49)`.
- **Lemma 3.6** (no same-rank escalation) is stated in integral form: `T` omits
  every nonzero square multiple of its truant. For the eight regular ternaries
  this is `OddPrime.not_represents_sq_mul` and `TwoAdic.exceptional_sq_mul`
  (`TwoAdic.not_represents_sq_mul_111`, …; `k = 1` gives
  `not_represents_truant_111`, …), and `Form.extension_posDef`
  (`Escalation/QuaternaryEscalation.lean`) turns it into positive definiteness
  of `T + ℤu`, that is, rank 4. For `f` it is
  `EscalatorF.not_represents_sq_mul_truant`, from the 7-adic obstruction of
  Proposition 3.3. The unary case is `Form.unitRemainder_of_eval_two`
  (`Escalation/Pairing.lean`): the remainder has norm 1 or 2. The binary cases
  are `Form.unitPairRemainder_of_eval_three` (`Escalation/BinaryOneOne.lean`),
  where the remainder has norm 1, 2, or 3, and `Form.oneTwoRemainder_ne_zero`
  (`Escalation/BinaryOneTwoRank.lean`).

## §4 Extensions of the ternary escalators

- **§4.1 and Lemma 4.1** are formalized for an arbitrary ternary `T`
  (`Forms/QuaternaryExtension.lean`):
  - changing the generator by `a ∈ ℤ³` (`shift`) moves `c` to `c + G_T a`
    without changing the represented values; `exists_shift_diag` gives the
    representatives for diagonal `T`;
  - `d = det / gcd(det, α)` and `β = α / gcd(det, α)` with `α = adj(G_T) c`,
    so `G_T β = d c`; that `d` is the least index with `d G_T⁻¹ c` integral
    is not proven, and nothing uses it;
  - `q` is the norm of `(-β, d)`; `eval_orthogonal` and `represents_of_sub`
    give the containment of Lemma 4.1 (every value of `T ⊥ ⟨q⟩` is a value
    of `M`), and `q_pos` its positivity. That `T ⊥ ⟨q⟩` has index `d` in `M`
    is not formalized; the proof uses only the containment. Part (ii) is
    `scaled_eval`;
  - `q` and `d` do not depend on the generator (`q_shift`, `index_shift`).

  The representatives of Table 2 for the diagonal escalators come from
  `exists_shift_diag`; those for `g` and `f` are `TwoAdic.exists_rep_g` and
  `EscalatorF.exists_rep`. The range `m ≤ 31` for `f` is not stated; the
  proof bounds `q` directly.
- **Lemma 4.2.** That `d` divides `det G_T` is `det_eq`, and equation (3) is
  `exists_truant_equation`. The bounds (4) and (5) and the range of `m` are
  `q_le_index_sq_mul`, `q_le_det_sq_mul`, and `det_mul_m_le`, all over `ℤ`
  (for example `det·m ≤ det·τ + cᵀ adj(G_T) c`). They are stated for every
  value `τ` represented by `M` and omitted by `T`, not only for the truant
  (stronger).
- **Lemma 4.3** is `Escalator113.not_nine_dvd_q` and
  `Escalator125.not_twentyfive_dvd_q`, stated for every extension
  representing the truant, with the manuscript's cases. Where the manuscript
  cites (3), for the representatives with `p ∤ d`, Lean writes out the
  identity (2) for that representative (`d = 1`, and `d = 2` for
  `c = (0, 1, 0)`); the normalization `k ≥ 1` is not needed.
- **Lemma 4.4** is `EscalatorF.q_mem_coefficients`: `q ∈ Q₇`, and `M`
  contains `f ⊥ ⟨q⟩` by Lemma 4.1. The cases of its proof are
  `EscalatorF.q_cases`. The 82 values of `q` are `irregularCoefficients`
  (length checked). As in the manuscript, 14 is excluded because `f` omits
  21 and 7.

## §5 Extensions of the regular ternaries

- **§5.1** (`Regular/TwoAdicEscalators.lean`, `Regular/TwoAdicFibonacci.lean`,
  `Regular/TwoAdicExtensions.lean`, `Regular/TwoAdicUniversality.lean`) follows
  the manuscript's structure. The exceptional families are
  `TwoAdic.TwoAdicExceptional ε r` (`Regular/TwoAdicSubtraction.lean`), and the
  2-adic rows of Proposition 3.2 are `represents111_iff`, …,
  `represents123_iff`.
- **Lemma 5.2** (`Regular/TwoAdicEscalators.lean`). Part (i) is `sub_of_high`
  and `exceptional_sub_of_high`; part (ii) is `exists_sub_escape`, assembled
  from the five bounded rows and the two far cases of
  `Regular/TwoAdicSubtraction.lean`.
- **Lemma 5.3.** Part (i) is `three_le_of_odd`: valuation 1 is excluded by
  `Fₙ mod 16 ∉ {10, 14}`. Part (ii) (`size_bound_even_seven`,
  `size_bound_odd`) uses the manuscript's indices 34 and 64 and Lemma 2.1. At
  `F₂₂ = 17711` the manuscript uses `F₂₂ > 4 · 22 · 55` for `⟨1,1,1⟩` and
  `F₂₂ > 16 · 880` for `⟨1,2,2⟩`; Lean checks `F₂₂ ≥ 16 q̄_T` for every
  `q̄_T ≤ 880`, which covers both. The members of the families below `F₆₄` come from
  the table of Lemma 2.4 rather than from Lemma 2.2.
- **Lemma 5.4** (`not_represents_of_high`) follows the manuscript: `d² τ − q
  w²` is a value of `T` with the same valuation and odd part as `τ`. Lean
  applies the identity (2) (`scaled_eval`) directly, without the
  normalization `k ≥ 1` of (3). It is stated for any ternary `T` whose values
  avoid `E_{ε,r}` and for every member `2^v u` of `E_{ε,r}`, not only for the
  truant of one of the six ternaries (stronger); the proof applies it only to
  the truants.
- **Lemma 5.5** (`g_represents_F22`) follows the manuscript's cases.
- **Lemma 5.6** (`not_high_124`) follows the manuscript; the odd-`w` case
  checks `x² + 2y² ≢ 7, 15 (mod 16)` over `ℤ/16`.
- **Proposition 5.7** is `not_high_111`, `not_high_g`, `not_high_112`,
  `not_high_123`, `not_high_124`, and, for `⟨1,2,2⟩`, `high_122` with the
  converse `extension122_universal` (the fourteen extensions are positive
  definite, have `v₂(q) = 3`, represent 55, and are Fibonacci-universal).
  For `m ≡ 1 (mod 4)` the omission of 55 splits on the parity of `w`, as in
  the manuscript; for odd `w` the residue modulo 4 already suffices. For the
  even exceptions, the size hypothesis uses `q = 4(m − 1) ≤ 216` directly,
  where the manuscript invokes (5).
- **Proposition 5.1** is `fibonacciUniversal_111`, `_122`, `_g`, `_112`,
  `_124`, `_123`; `fibonacciUniversal_of_room` is the case
  `v₂(q) ≤ v₂(τ) + 2`. Of `extension122_universal`, the proof uses only the
  last part, universality; the other parts record the manuscript's
  description of the fourteen extensions.
- **Lemmas 5.8 and 5.10** are single statements for both primes
  (`OddPrime.represents_phi`, `OddPrime.exists_sub_represents`), with
  Proposition 3.2 for `⟨1,1,3⟩` and `⟨1,2,5⟩` in valuation form
  (`OddPrime.represents_iff`). In Lemma 5.8, `X² + αY² ≡ 0 (mod p)` forcing
  `p ∣ X, Y` is the anisotropy used for the obstructions of Proposition 3.2
  (`OddPrime.dvd_of_dvd_sq_add`).
- **Lemma 5.9** is formalized for every prime `p ≥ 5`
  (`exists_sub_mul_sq_square`, `Arithmetic/QuadraticCongruence.lean`) with the
  manuscript's character-sum count: `Σ_t χ(t² − ξ) = −1`
  (`sum_quadraticChar_sq_sub`), so the conic `x² + q₀t² = u₀` has `p − χ(−q₀) ≥
  p − 1` points, at most two with `x = 0` (`exists_conic_point`). Lemma 5.10
  uses it for `p = 5`, and Lemma 6.3 for `p = 7`.
- **Propositions 5.11 and 5.12** (`Escalator113.fibonacciUniversal`,
  `Escalator125.fibonacciUniversal`) follow the manuscript, with its
  representatives, its bounds `m ≤ 988` and `m ≤ 611`, its cutoffs
  `F₂₈/84` and `F₂₅/25`, and, for `F₂₀` and `338 < b < 488`, the step
  `w = ±1` and the values `b = 378, 478`. The Fibonacci exceptions after the
  truant (`exception_data`) are located by periodicity (`obstructed_index`,
  as for Lemma 2.4) and the explicit factorizations of `F₄, F₈, F₁₂, F₂₄`
  and `F₅, F₁₀`; Lemma 2.2 enters only through the bound (1) in the size
  estimates.

## §6 Extensions of `f`

- **The hypothesis `hclass`.** Propositions 3.5, 6.1, and 6.2 and Lemmas 6.4
  and 6.5 take the sufficiency direction of Proposition 3.3 as the hypothesis
  `hclass`: every `ResidualEligible` integer is represented by `f` or by `h`.
  `Criterion.Sufficiency` passes it from the classical results.
- **Proposition 6.2** (`representsFPlus_seven`) uses the manuscript's table of
  `w`, checked on every class modulo 84, and the same two exceptional values.
  The remark that universality also follows from the Fifteen Theorem is not
  formalized.
- **Lemma 6.3** (`exists_seven_choice`) follows the manuscript, with Lemma 5.9
  at `p = 7`; the choice of `k` is an integer whose class modulo 7 is used. It
  is stated for every integer `N`, and its conclusion (`EligibleResidue`) is
  that the difference is eligible and not divisible by 49.
- **Lemma 6.4** (`representsFPlus_small_subtraction`) follows the manuscript.
- **Lemmas 6.3, 6.4, and 6.5** are stated for every `q` that is prime to 7 or
  7 times a nonsquare modulo 7 (positive in Lemma 6.4), not only for
  `q ∈ Q₇ \ {7}` (stronger); `irregularCoefficient_facts` gives this condition
  for the elements of `Q₇` other than 7.
- **Proposition 6.1** is `EscalatorF.fibonacciUniversal`, stated for
  quaternary extensions of `f`; the tail `n ≥ 48` is
  `representsFPlus_fib_of_forty_eight_le`. The bounds `⌊7p²/2⌋ ≤ k̄ = 41583` for
  `p ∈ P₇`, `B* = 1022·k̄² < F₆₁`, and `441·1022 < F₄₈` are checked as in the
  manuscript (`coverPrimes_checked`, `fib_growth_values`).
- **Lemma 6.5** (`representsFPlus_of_local_root`) lifts the root modulo `p²` by
  one elementary Newton step (`Arithmetic/RootLifting.lean`) and uses centered
  CRT (`Arithmetic/CenteredCRT.lean`). It is stated for every odd prime of
  Table 3, so it also allows `p = 3`, which the proof does not use.
- **Lemma 6.6** (`Irregular/RestrictedCover.lean`) follows the manuscript's
  eight groups of values of `q` and their primes. For each group, a checked walk of
  the Fibonacci state modulo 12 and the group's primes through one return time
  (72, 120, 168, or 216) verifies the case analysis on every residue class of
  the index, and proves that the time is a return time.
  - The manuscript argues by quadratic characters; the checker finds a nonzero
    `k < p` with `q k² ≡ Fₙ (mod p)`, which is equivalent.
  - The checker asks for a root only on the classes where `(q, Fₙ)` meets a
    pair in (7). For the values of `q` that the manuscript treats at both parities
    although (7) requires only one, Lean checks only the parity (7) requires.
  - The per-prime periods of Table 3 (20, 10, 28, …, 108) are not stated;
    only the common return time of each group is checked.
- **The small-prime table** for `n = 57, 58` has one row per pair
  `(n, q)` with its prime and root (`smallPrimeTable`), twenty-seven rows in
  all; the
  manuscript groups them into five rows by prime. Each row checks its own
  subtraction bound `q ⌊7p²/2⌋² < Fₙ` in place of the manuscript's uniform
  bound `1022 · 1263² < F₄₈`.
- **Table 3** lists the same twelve matrices (`Irregular/Transfers.lean`); each
  identity is checked by `ring`.

## §7 The criterion and its minimality

- **Sufficiency** (`Criterion.Sufficiency`) follows the manuscript's proof of
  Theorem 1.1. `escalator_extensions` records, for each of the nine
  escalators, positive definiteness, Lemma 3.6, and the
  Fibonacci-universality of its extensions representing the truant
  (Propositions 5.1, 5.11, 5.12, 6.1); `criterionSufficiency_of_classical`
  combines it with the escalation and `Form.fibonacciUniversal_of_frame`.
  The ambient form may have any finite rank.
- **The four-square extension** follows the manuscript
  (`Criterion/FourSquareExtension.lean`, `Criterion/Truants.lean`), with the
  large rank kept symbolic.
- **The Table 1 congruence check** (`Criterion/TableOne.lean`,
  `Criterion/TableOneCongruences.lean`) uses `2f = 2x² + (2y+z)² + 7z²` modulo
  49 for the row of `f`; the manuscript states that `f` modulo 49 omits 21. The
  two are equivalent, since 2 is a unit modulo 49. In the minimality proof Lean
  takes the omission of `t` by `P_t` from this check
  (`tableOneRow_polynomial_omits`); the manuscript takes it from §3 and gives
  the congruence as an independent check.
- **Representation below each truant** (`tableOneRow_represents_below`) uses
  displayed vectors for the zero, unary, and binary escalators, and
  `truant_column` for the six ternary ones. Lean's indispensability
  therefore takes the criteria of Proposition 3.2 as input
  (`criterionIndispensability_of_classical`). `Criterion/Theorem.lean`
  supplies them.

## §8 Concluding remarks

- **Proposition 8.1** and the remarks on other sequences are not formalized.
  Lemma 6.5 is the instance of Proposition 8.1 that the proof uses.

## Finite checks in the Lean proof

Every finite check is a Lean proposition, proven by kernel evaluation, with a
soundness lemma that turns it into a statement about all integers or
indices.

- The table of `v₂(Fₙ)` and `u₂(Fₙ)` for `n ≤ 64`
  (`Regular/TwoAdicFibonacci.lean`), explicit Fibonacci values, and Fibonacci
  return times.
- Lemma 2.2, each over one return time (`Fibonacci/SmallModuli.lean`,
  `Fibonacci/Twofold.lean`, `Fibonacci/Threefold.lean`,
  `Fibonacci/Fivefold.lean`): divisibility of `Fₙ` by 2, 3, 4, 5, 8, 9, and
  16, the residues 10 and 14 modulo 16, and the cofactor of `5Fₘ` in `F₅ₘ`
  modulo 5.
- Residue checks: Lemma 3.4 over `(ℤ/6)³`, the table of Proposition 6.2 modulo
  84, the eligibility of square multiples modulo 49, Lemma 5.6 over `ℤ/16`,
  the 7-adic descent for `f` over `ℤ/7` (`Irregular/EscalatorF.lean`), and
  square residues.
- Proposition 3.5: the vectors for `F₀, …, F₇`, the six witnesses, and the
  window below 48
  (`Irregular/InitialWindow.lean`).
- Lemma 4.4: the 82 values of `q` and their facts
  (`irregularCoefficients_length`, `irregularCoefficients_checked`, in
  `Irregular/Subtraction.lean`).
- Lemma 6.6: the eight group walks and the assignment of the twenty
  values of `q` to the groups (`Irregular/RestrictedCover.lean`).
- Proposition 6.1 (`Irregular/LargeIndices.lean`): the small-prime table and its
  completeness, the residues of `F₄₈, …, F₆₀` modulo 12, the facts about the
  cover primes, the values of `q` that can meet (7), and the bounds
  `441·1022 < F₄₈` and `1022·41583² < F₆₁`; the transfer primes
  (`transfer_prime_facts_checked`).
- Table 1: the congruence checks, the indices of the truants, and the equality
  of `criterion` with the set of truants.
- Classical inputs:
  - the lists of reduced Gram matrices of determinants 3, 6, 7, and 10, from
    one shared search (`ClassicalInputs/Reduction/Classification.lean`), with
    explicit unimodular equivalences to the class representatives at 3, 6, and
    10;
  - the mod-7 zero counts.

The residue tables of the Mordell constructions are proven by case analysis
(`interval_cases`, `omega`); they are not kernel checks.

No file outside `FibonacciCriterion/` is read by the proof.
