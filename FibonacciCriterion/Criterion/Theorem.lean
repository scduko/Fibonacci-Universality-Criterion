import FibonacciCriterion.Criterion.Proof
import FibonacciCriterion.ClassicalInputs.Theorems

/-!
# The Fibonacci criterion (Theorem 1.1)

Combines `Criterion.Proof`, which proves the criterion from the classical
results in `FibonacciClassicalInputs`, with the proof of those results in
`ClassicalInputs.Theorems` (`fibonacciClassicalInputs`). The theorems
here do not take the classical results as a hypothesis.
-/

namespace FibonacciCriterion

/-- A form that represents every element of `criterion` is Fibonacci-universal
(part of Theorem 1.1). -/
theorem criterionSufficiency : CriterionSufficiency :=
  criterionSufficiency_of_classical fibonacciClassicalInputs

/-- Every set of Fibonacci numbers whose representation forces
Fibonacci-universality contains `criterion` (part of Theorem 1.1). -/
theorem criterionIndispensability : CriterionIndispensability :=
  criterionIndispensability_of_classical fibonacciClassicalInputs.representation

/-- For each `t` in `criterion`, some positive-definite form represents every
Fibonacci number other than `t` and does not represent `t` (§7). -/
theorem exists_criterion_omission (t : ℕ) (ht : t ∈ criterion) :
    ∃ (r : ℕ) (V : Form (Fin r ⊕ (Fin 4 ⊕ Fin (t + 1)))),
      (¬ V.Represents t) ∧
      (∀ n : ℕ, Nat.fib n ≠ t → V.Represents (Nat.fib n)) :=
  exists_criterion_omission_of_classical fibonacciClassicalInputs.representation t ht

/-- Corollary 1.2, first statement: a form that represents `F₁, …, F₄₂` is
Fibonacci-universal. -/
theorem fibonacciUniversal_of_represents_fib_le_42 {ι : Type} [Fintype ι] (Q : Form ι)
    (h : ∀ n : ℕ, 1 ≤ n → n ≤ 42 → Q.Represents (Nat.fib n)) :
    FibonacciUniversal Q :=
  fibonacciUniversal_of_represents_fib_le_42_of_classical fibonacciClassicalInputs Q h

/-- Corollary 1.2, second statement: the index 42 cannot be lowered, since
representing `F₀, …, F₄₁` does not force Fibonacci-universality. -/
theorem not_isFibonacciCriterion_fib_le_41 :
    ¬ IsFibonacciCriterion {s : ℕ | ∃ n : ℕ, n ≤ 41 ∧ Nat.fib n = s} :=
  not_isFibonacciCriterion_fib_le_41_of_classical fibonacciClassicalInputs

/-- Theorem 1.1: a form of any finite rank is Fibonacci-universal if and only
if it represents every element of `criterion`; every Fibonacci criterion set
contains `criterion`; `criterion` is a minimal Fibonacci criterion set; and it
is the only one. -/
theorem fibonacci_criterion :
    (∀ {ι : Type} [Fintype ι] (Q : Form ι),
        FibonacciUniversal Q ↔ ∀ t ∈ criterion, Q.Represents t) ∧
      (∀ S : Set ℕ, IsFibonacciCriterionSet S →
        (criterion : Set ℕ) ⊆ S) ∧
      IsMinimalFibonacciCriterionSet (criterion : Set ℕ) ∧
      ∀ S : Set ℕ, IsMinimalFibonacciCriterionSet S →
        S = (criterion : Set ℕ) :=
  fibonacci_criterion_of_classical fibonacciClassicalInputs

open scoped Matrix in
/-- Theorem 1.1 for an integer matrix `G` that is positive definite over `ℝ` in
Mathlib's sense: the quadratic form `x ↦ x ⬝ᵥ G *ᵥ x` represents every
Fibonacci number if and only if it represents every element of `criterion`. -/
theorem fibonacci_criterion_matrix {ι : Type} [Fintype ι] (G : Matrix ι ι ℤ)
    (hG : (G.map (Int.cast : ℤ → ℝ)).PosDef) :
    (∀ k : ℕ, ∃ x : ι → ℤ, x ⬝ᵥ G *ᵥ x = (Nat.fib k : ℤ)) ↔
      ∀ t ∈ criterion, ∃ x : ι → ℤ, x ⬝ᵥ G *ᵥ x = (t : ℤ) := by
  have h := fibonacci_criterion.1 (Form.ofPosDef G hG)
  simpa only [FibonacciUniversal, Form.ofPosDef_represents_iff] using h

end FibonacciCriterion
