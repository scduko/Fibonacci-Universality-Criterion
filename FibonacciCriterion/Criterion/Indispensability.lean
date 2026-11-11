import FibonacciCriterion.Criterion.Truants
import FibonacciCriterion.Criterion.TableOneForms
import FibonacciCriterion.Criterion.TableOneCongruences
import FibonacciCriterion.Escalation.TernaryTruants
import FibonacciCriterion.Statement

/-!
# Minimality of the criterion (§7)

For each `t` in `criterion`, the escalator `P_t` of Table 1 omits `t`, by the
congruence check of Table 1, and represents every smaller Fibonacci number: by
displayed vectors for the escalators of rank at most 2, and by the truant
column of Figure 1 (`truant_column`) for the six ternary ones. The four-square
extension of `P_t` therefore represents every Fibonacci number except `t`
(`exists_criterion_omission_of_classical`), so every Fibonacci criterion set
contains `t` (`criterionIndispensability_of_classical`).

The criteria of Proposition 3.2 enter through `ClassicalRepresentation.Inputs`;
the determinant-7 result (Proposition 3.3) is not used.
-/

namespace FibonacciCriterion

/-- Each escalator `P_t` of Table 1 represents `Fₙ` for every `n` below the
index of its truant: by displayed vectors for the escalators of rank at most
2, and by the truant column of Figure 1 (`truant_column`) for the six ternary
ones. -/
theorem tableOneRow_represents_below (c : ClassicalRepresentation.Inputs) (i : Fin 10)
    (n : ℕ) (hn : n < (tableOneRow i).index) :
    ∃ v : IntTriple, (tableOneRow i).eval v = (Nat.fib n : ℤ) := by
  fin_cases i <;>
    simp only [tableOneRow, tableOne, List.get, TableOneRow.eval] at hn ⊢
  · interval_cases n
    exact ⟨(0, 0, 0), by norm_num⟩
  · interval_cases n
    · exact ⟨(0, 0, 0), by norm_num⟩
    · exact ⟨(1, 0, 0), by norm_num⟩
    · exact ⟨(1, 0, 0), by norm_num [Nat.fib_two]⟩
  · interval_cases n
    · exact ⟨(0, 0, 0), by norm_num⟩
    · exact ⟨(1, 0, 0), by norm_num⟩
    · exact ⟨(1, 0, 0), by norm_num [Nat.fib_two]⟩
    · exact ⟨(1, 1, 0), by norm_num [Nat.fib_add_two]⟩
  · interval_cases n
    · exact ⟨(0, 0, 0), by norm_num⟩
    · exact ⟨(1, 0, 0), by norm_num⟩
    · exact ⟨(1, 0, 0), by norm_num [Nat.fib_two]⟩
    · exact ⟨(0, 1, 0), by norm_num [Nat.fib_add_two]⟩
    · exact ⟨(1, 1, 0), by norm_num [Nat.fib_add_two]⟩
  · obtain ⟨x, y, z, h⟩ := (truant_column c (b := 2) (d := 4) (e := 1)
      (by norm_num [NineTernaryEscalator])).1 n (by norm_num [escalatorTruantIndex]; omega)
    exact ⟨(x, y, z), by rw [← h]; simp only [TernaryGram.eval]; ring⟩
  · obtain ⟨x, y, z, h⟩ := (truant_column c (b := 1) (d := 1) (e := 0)
      (by norm_num [NineTernaryEscalator])).1 n (by norm_num [escalatorTruantIndex]; omega)
    exact ⟨(x, y, z), by rw [← h]; simp only [TernaryGram.eval]; ring⟩
  · obtain ⟨x, y, z, h⟩ := (truant_column c (b := 2) (d := 5) (e := 0)
      (by norm_num [NineTernaryEscalator])).1 n (by norm_num [escalatorTruantIndex]; omega)
    exact ⟨(x, y, z), by rw [← h]; simp only [TernaryGram.eval]; ring⟩
  · obtain ⟨x, y, z, h⟩ := (truant_column c (b := 1) (d := 3) (e := 0)
      (by norm_num [NineTernaryEscalator])).1 n (by norm_num [escalatorTruantIndex]; omega)
    exact ⟨(x, y, z), by rw [← h]; simp only [TernaryGram.eval]; ring⟩
  · obtain ⟨x, y, z, h⟩ := (truant_column c (b := 2) (d := 3) (e := 0)
      (by norm_num [NineTernaryEscalator])).1 n (by norm_num [escalatorTruantIndex]; omega)
    exact ⟨(x, y, z), by rw [← h]; simp only [TernaryGram.eval]; ring⟩
  · obtain ⟨x, y, z, h⟩ := (truant_column c (b := 1) (d := 2) (e := 0)
      (by norm_num [NineTernaryEscalator])).1 n (by norm_num [escalatorTruantIndex]; omega)
    exact ⟨(x, y, z), by rw [← h]; simp only [TernaryGram.eval]; ring⟩

/-- For each row of Table 1, a positive-definite form, the escalator `P_t`,
omits the truant `t` and represents every Fibonacci number below `t`. -/
theorem tableOneRow_is_truant (c : ClassicalRepresentation.Inputs) (i : Fin 10) :
    ∃ (r : ℕ) (P : Form (Fin r)),
      (¬ P.Represents (tableOneRow i).truant) ∧
      (∀ n : ℕ, Nat.fib n < (tableOneRow i).truant →
        P.Represents (Nat.fib n)) := by
  obtain ⟨r, P, hP⟩ := tableOneRow_realizable i
  refine ⟨r, P, ?_, ?_⟩
  · intro h
    exact tableOneRow_polynomial_omits i ((hP _).mp h)
  · intro n hn
    apply (hP _).mpr
    apply tableOneRow_represents_below c i n
    by_contra h
    have hle : (tableOneRow i).index ≤ n := Nat.le_of_not_gt h
    have hmono := Nat.fib_mono hle
    rw [tableOneRow_fib i] at hmono
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `criterion` is the set of truants of the ten rows of Table 1. -/
theorem criterion_eq_tableOne_truants :
    criterion = (Finset.univ : Finset (Fin 10)).image
      (fun i => (tableOneRow i).truant) := by
  decide +kernel

/-- For each `t` in `criterion`, some positive-definite form represents every
Fibonacci number other than `t` and omits `t` (§7). Its rank stays symbolic. -/
theorem exists_criterion_omission_of_classical (c : ClassicalRepresentation.Inputs)
    (t : ℕ) (ht : t ∈ criterion) :
    ∃ (r : ℕ) (V : Form (Fin r ⊕ (Fin 4 ⊕ Fin (t + 1)))),
      (¬ V.Represents t) ∧
      (∀ n : ℕ, Nat.fib n ≠ t → V.Represents (Nat.fib n)) := by
  rw [criterion_eq_tableOne_truants] at ht
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
  obtain ⟨r, P, hmiss, hlower⟩ := tableOneRow_is_truant c i
  have hmiss' : ¬ P.Represents t := by simpa only [hi] using hmiss
  have hlower' : ∀ n : ℕ, Nat.fib n < t → P.Represents (Nat.fib n) := by
    simpa only [hi] using hlower
  obtain ⟨V, hV⟩ := exists_fibonacci_omission P t hmiss' hlower'
  exact ⟨r, V, hV⟩

/-- Given the classical representation results, every set of Fibonacci numbers
whose representation forces Fibonacci-universality contains `criterion` (part
of Theorem 1.1). Only the criteria of Proposition 3.2 are used. `Criterion.Proof`
combines this with sufficiency (`criterionSufficiency_of_classical`). -/
theorem criterionIndispensability_of_classical (c : ClassicalRepresentation.Inputs) :
    CriterionIndispensability := by
  intro S hS hcriterion t ht
  change t ∈ criterion at ht
  rw [criterion_eq_tableOne_truants] at ht
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
  obtain ⟨r, P, hmiss, hlower⟩ := tableOneRow_is_truant c i
  have htFib : ∃ n : ℕ, Nat.fib n = (tableOneRow i).truant :=
    ⟨(tableOneRow i).index, tableOneRow_fib i⟩
  have hmem := criterion_contains_truant S hS hcriterion P
    (tableOneRow i).truant htFib hmiss hlower
  simpa only [hi] using hmem

end FibonacciCriterion
