import FibonacciCriterion.Criterion.Sufficiency
import FibonacciCriterion.Criterion.Indispensability

/-!
# The criterion from the classical results (Theorem 1.1)

Proves Theorem 1.1 with the classical results in `FibonacciClassicalInputs` as
a hypothesis (`fibonacci_criterion_of_classical`): a positive-definite form
with an integral symmetric Gram matrix, of any finite rank, is
Fibonacci-universal if and only if it represents every element of
`criterion`; every Fibonacci criterion set contains `criterion`; and
`criterion` is the unique minimal Fibonacci criterion set. It also proves that
representing `F₁, …, F₄₂` suffices and that the index 42 cannot be lowered
(Corollary 1.2).

The proof has four parts:

1. `Statement` defines the set `criterion`, Fibonacci criterion sets, and the
   statements of sufficiency and indispensability.
2. The escalation of Proposition 3.1 (`Escalation.NineTernaryFrames`) finds a
   frame of one of the nine ternary escalators in every form that represents
   1, 2, 3, and 5.
3. `Criterion.Sufficiency` follows §7: together with a vector of truant norm,
   the frame spans a quaternary extension of rank 4 (Lemma 3.6), which is
   Fibonacci-universal by Propositions 5.1, 5.11, 5.12, and 6.1
   (`Regular.TwoAdicUniversality`, `Regular.Escalator113`,
   `Regular.Escalator125`, `Irregular.EscalatorF`).
4. `Criterion.Indispensability` follows §7: for each `t` in `criterion`, it
   extends the escalator `P_t` of Table 1 to a form that represents every
   Fibonacci number except `t`, so every Fibonacci criterion set contains
   `t`. This module combines it with sufficiency to obtain minimality and
   uniqueness.

The hypothesis consists of the criteria of Proposition 3.2 for `⟨1,1,1⟩`,
`⟨1,1,3⟩`, `⟨1,2,3⟩`, and `⟨1,2,5⟩`, the sufficiency direction of
Proposition 3.3, and the Fibonacci valuation formulas at 2, 3, and 5
(Lemma 2.2). Sufficiency uses it. The containment of `criterion` in every
Fibonacci criterion set uses only the criteria of Proposition 3.2, which show
that the five regular ternary escalators of Table 1 represent the Fibonacci
numbers below their truants; the other five rows have displayed vectors.
Necessity uses no hypothesis. `ClassicalInputs.Theorems` proves the
classical results, by Mordell constructions, reciprocity, reduction, and
finite classification; `Criterion.Theorem` supplies them and proves
`fibonacci_criterion`.
-/

namespace FibonacciCriterion

/-- Every element of `criterion` is a Fibonacci number of positive index. -/
theorem criterion_subset_fibonacciValues :
    (criterion : Set ℕ) ⊆ fibonacciValues := by
  intro s hs
  have hs' : s ∈ criterion := Finset.mem_coe.mp hs
  rw [← fib_criterionIndices] at hs'
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs'
  refine ⟨n, ?_, rfl⟩
  simp only [criterionIndices, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

/-- Given the classical results, a form is Fibonacci-universal if and only if
it represents every element of `criterion` (part of Theorem 1.1). Only the
reverse implication uses the classical results. -/
theorem fibonacciUniversal_iff_represents_criterion
    (i : FibonacciClassicalInputs) {ι : Type} [Fintype ι] (Q : Form ι) :
    FibonacciUniversal Q ↔ ∀ t ∈ criterion, Q.Represents t :=
  ⟨represents_criterion_of_universal Q, fun h =>
    criterionSufficiency_of_classical i ι Q fun s hs => h s (Finset.mem_coe.mp hs)⟩

/-- Given the classical results, every Fibonacci criterion set contains
`criterion` (part of Theorem 1.1). -/
theorem criterion_subset_of_isFibonacciCriterionSet (i : FibonacciClassicalInputs)
    {S : Set ℕ} (hS : IsFibonacciCriterionSet S) : (criterion : Set ℕ) ⊆ S :=
  criterionIndispensability_of_classical i.representation S
    (by
      intro s hs
      obtain ⟨n, -, hn⟩ := hS.2.1 hs
      exact ⟨n, hn⟩)
    hS.2.2

/-- Given the classical results, `criterion` is a Fibonacci criterion set. -/
theorem criterion_isFibonacciCriterionSet (i : FibonacciClassicalInputs) :
    IsFibonacciCriterionSet (criterion : Set ℕ) :=
  ⟨criterion.finite_toSet, criterion_subset_fibonacciValues,
    criterionSufficiency_of_classical i⟩

/-- Given the classical results, `criterion` is a minimal Fibonacci criterion
set. -/
theorem criterion_isMinimalFibonacciCriterionSet (i : FibonacciClassicalInputs) :
    IsMinimalFibonacciCriterionSet (criterion : Set ℕ) :=
  ⟨criterion_isFibonacciCriterionSet i, fun _ hT hsub =>
    Set.Subset.antisymm hsub (criterion_subset_of_isFibonacciCriterionSet i hT)⟩

/-- Given the classical results, `criterion` is the only minimal Fibonacci
criterion set. -/
theorem eq_criterion_of_isMinimalFibonacciCriterionSet
    (i : FibonacciClassicalInputs) {S : Set ℕ}
    (hS : IsMinimalFibonacciCriterionSet S) : S = (criterion : Set ℕ) :=
  (hS.2 _ (criterion_isFibonacciCriterionSet i)
    (criterion_subset_of_isFibonacciCriterionSet i hS.1)).symm

/-- Theorem 1.1: given the classical results,

1. a form of any finite rank is Fibonacci-universal if and only if it
   represents `1, 2, 3, 5, 21, 55, 610, 987, 832040, 267914296`;
2. every Fibonacci criterion set contains these ten numbers;
3. they form a minimal Fibonacci criterion set; and
4. they form the only minimal Fibonacci criterion set. -/
theorem fibonacci_criterion_of_classical (i : FibonacciClassicalInputs) :
    (∀ {ι : Type} [Fintype ι] (Q : Form ι),
        FibonacciUniversal Q ↔ ∀ t ∈ criterion, Q.Represents t) ∧
      (∀ S : Set ℕ, IsFibonacciCriterionSet S → (criterion : Set ℕ) ⊆ S) ∧
      IsMinimalFibonacciCriterionSet (criterion : Set ℕ) ∧
      ∀ S : Set ℕ, IsMinimalFibonacciCriterionSet S → S = (criterion : Set ℕ) :=
  ⟨fun Q => fibonacciUniversal_iff_represents_criterion i Q,
    fun _ hS => criterion_subset_of_isFibonacciCriterionSet i hS,
    criterion_isMinimalFibonacciCriterionSet i,
    fun _ hS => eq_criterion_of_isMinimalFibonacciCriterionSet i hS⟩

/-- Corollary 1.2, first statement: given the classical results, a form that
represents `F₁, …, F₄₂` is Fibonacci-universal. -/
theorem fibonacciUniversal_of_represents_fib_le_42_of_classical
    (i : FibonacciClassicalInputs) {ι : Type} [Fintype ι] (Q : Form ι)
    (h : ∀ n : ℕ, 1 ≤ n → n ≤ 42 → Q.Represents (Nat.fib n)) :
    FibonacciUniversal Q := by
  refine (fibonacciUniversal_iff_represents_criterion i Q).2 ?_
  intro t ht
  rw [← fib_criterionIndices] at ht
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
  simp only [criterionIndices, Finset.mem_insert, Finset.mem_singleton] at hn
  exact h n (by omega) (by omega)

/-- Corollary 1.2, second statement: the escalator `⟨1,1,2⟩` represents every
Fibonacci number below `F₄₂` and omits `F₄₂`, so representing `F₀, …, F₄₁`
does not force Fibonacci-universality. Of the classical results, only the
three-square theorem is used, through the criterion for `⟨1,1,2⟩` of
Proposition 3.2. -/
theorem not_isFibonacciCriterion_fib_le_41_of_classical (i : FibonacciClassicalInputs) :
    ¬ IsFibonacciCriterion {s : ℕ | ∃ n : ℕ, n ≤ 41 ∧ Nat.fib n = s} := by
  intro h
  obtain ⟨hbelow, hmiss⟩ := truant_column i.representation (b := 1) (d := 2) (e := 0)
    (by norm_num [NineTernaryEscalator])
  let P := TableOneForms.ternary 1 1 2 one_pos one_pos two_pos
  have hP : ∀ N : ℕ, P.Represents N ↔ (escalatorGram 1 2 0).Represents N := by
    intro N
    rw [TableOneForms.ternary_represents_iff]
    constructor
    · rintro ⟨⟨x, y, z⟩, hv⟩
      exact ⟨x, y, z, by rw [← hv]; simp only [TernaryGram.eval]; ring⟩
    · rintro ⟨x, y, z, hv⟩
      exact ⟨(x, y, z), by rw [← hv]; simp only [TernaryGram.eval]; ring⟩
  have hU := h (Fin 3) P (by
    rintro s ⟨n, hn, rfl⟩
    exact (hP _).2 (hbelow n (by norm_num [escalatorTruantIndex]; omega)))
  have h42 : escalatorTruantIndex 1 2 0 = 42 := by norm_num [escalatorTruantIndex]
  rw [escalatorTruant, h42] at hmiss
  exact hmiss ((hP _).1 (hU 42))

end FibonacciCriterion
