import FibonacciCriterion.Forms

/-!
# The set `C` and the statements to prove

Defines `criterion`, the set
`C = {1, 2, 3, 5, 21, 55, 610, 987, 832040, 267914296}` of Theorem 1.1, and
proves that it consists of the Fibonacci numbers `Fₙ` with
`n ∈ {1, 3, 4, 5, 8, 10, 15, 16, 30, 42}` (`fib_criterionIndices`). The
Fibonacci numbers are Mathlib's `Nat.fib`, with `F₀ = 0` and `F₁ = 1`
(`fib_convention`). A Fibonacci-universal form therefore represents every
element of `C` (`represents_criterion_of_universal`).

The other two parts of Theorem 1.1 are stated here as propositions:
sufficiency (`CriterionSufficiency`) and the indispensability of every element
of `C` (`CriterionIndispensability`). `Criterion.Sufficiency` proves the first
and `Criterion.Indispensability` the second, from the classical results in
`FibonacciClassicalInputs`; `Criterion.Proof` combines them, and
`Criterion.Theorem` supplies the classical results.

The file also defines the manuscript's Fibonacci criterion sets and their
minimality (`IsFibonacciCriterionSet`, `IsMinimalFibonacciCriterionSet`).
With `Form`, `Form.Represents`, `FibonacciUniversal`, and
`IsFibonacciCriterion` from `Forms`, these are all the definitions in the
statement of the final theorem `fibonacci_criterion` (`Criterion.Theorem`).
`docs/STATUS.md` records the build and the axiom audit.
-/

namespace FibonacciCriterion

/-- The indices `n` of the Fibonacci numbers `Fₙ` in `criterion`. -/
def criterionIndices : Finset ℕ := {1, 3, 4, 5, 8, 10, 15, 16, 30, 42}

/-- The set `C` of Theorem 1.1. -/
def criterion : Finset ℕ :=
  {1, 2, 3, 5, 21, 55, 610, 987, 832040, 267914296}

/-- The Fibonacci numbers of the manuscript are Mathlib's `Nat.fib`:
`F₀ = 0`, `F₁ = 1`, and `Fₙ₊₂ = Fₙ₊₁ + Fₙ`. -/
theorem fib_convention :
    Nat.fib 0 = 0 ∧ Nat.fib 1 = 1 ∧
      ∀ n : ℕ, Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n :=
  ⟨Nat.fib_zero, Nat.fib_one, fun n => by rw [Nat.fib_add_two, add_comm]⟩

set_option maxRecDepth 100000 in
/-- The two descriptions of `C` in Theorem 1.1 agree: the Fibonacci numbers
`Fₙ` with `n` in `criterionIndices` form the set `criterion`, that is,
`{F₁, F₃, F₄, F₅, F₈, F₁₀, F₁₅, F₁₆, F₃₀, F₄₂} = C`. -/
theorem fib_criterionIndices : criterionIndices.image Nat.fib = criterion := by
  decide +kernel

/-- A Fibonacci-universal form represents every element of `criterion`. -/
theorem represents_criterion_of_universal {ι : Type} [Fintype ι]
    (P : Form ι) (hP : FibonacciUniversal P) :
    ∀ t ∈ criterion, P.Represents t := by
  intro t ht
  rw [← fib_criterionIndices] at ht
  obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp ht
  exact hP n

/-- The sufficiency statement of Theorem 1.1: every form that represents each
element of `criterion` is Fibonacci-universal. It is proven from the classical
results by `criterionSufficiency_of_classical`. -/
def CriterionSufficiency : Prop := IsFibonacciCriterion (criterion : Set ℕ)

/-- The indispensability statement of Theorem 1.1: every set of Fibonacci
numbers whose representation forces Fibonacci-universality contains
`criterion`. The set may be infinite and may contain `F₀ = 0`. It is proven by
`criterionIndispensability_of_classical` in `Criterion.Indispensability`. -/
def CriterionIndispensability : Prop :=
  ∀ S : Set ℕ,
    (∀ s ∈ S, ∃ n : ℕ, Nat.fib n = s) →
    IsFibonacciCriterion S → (criterion : Set ℕ) ⊆ S

/-! ### Fibonacci criterion sets -/

/-- The set `F = {Fₙ : n ≥ 1}` of the manuscript. It leaves out `F₀ = 0`,
which every form represents. -/
def fibonacciValues : Set ℕ := {s | ∃ n : ℕ, 1 ≤ n ∧ Nat.fib n = s}

/-- A Fibonacci criterion set: a finite subset of `fibonacciValues` whose
representation forces Fibonacci-universality. -/
def IsFibonacciCriterionSet (S : Set ℕ) : Prop :=
  S.Finite ∧ S ⊆ fibonacciValues ∧ IsFibonacciCriterion S

/-- A Fibonacci criterion set that is minimal with respect to inclusion. -/
def IsMinimalFibonacciCriterionSet (S : Set ℕ) : Prop :=
  IsFibonacciCriterionSet S ∧
    ∀ T : Set ℕ, IsFibonacciCriterionSet T → T ⊆ S → T = S

end FibonacciCriterion
