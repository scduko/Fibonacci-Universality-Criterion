import FibonacciCriterion.Irregular.ModTwelve
import FibonacciCriterion.Irregular.Eligibility

/-!
# Fibonacci numbers represented by `f` below index 48 (Proposition 3.5)

`representsF_fib_initial` is the representation part of Proposition 3.5:
`f` represents `Fₙ` for every `n < 48` other than 8, including `n = 0`. Below
index 8 and at the six indices `9, 10, 15, 33, 34, 39`, an explicit vector is
checked (`initialWitnesses_checked`; `representsF_fib_of_lt_eight` is the part
below index 8, which needs no hypothesis). At every other index from 9 to 47, `Fₙ`
is eligible and is not 7 or 10 modulo 12 (`initial_window_checked`), so the
sufficiency direction of Proposition 3.3 (the hypothesis `hclass`) and
Lemma 3.4 apply. That `f` omits `F₈ = 21` is `EscalatorF.not_represents_truant`.
That `F₄₈` is the next exception is not formalized.
-/

namespace FibonacciCriterion.Irregular

/-- Explicit representations `(n, x, y, z)` with `f(x, y, z) = Fₙ`. -/
def initialWitnesses : List (ℕ × ℤ × ℤ × ℤ) :=
  [(0, 0, 0, 0), (1, 1, 0, 0), (2, 1, 0, 0), (3, 0, 1, 0), (4, 1, 1, 0), (5, 1, 0, 1),
   (6, 0, 2, 0), (7, 3, 0, 1), (9, 4, 3, 0), (10, 3, 3, 2), (15, 12, 7, 8),
   (33, 12, 1051, 368), (34, 9, 1473, 322), (39, 12, 5289, 568)]

/-- Each entry `(n, x, y, z)` of `initialWitnesses` satisfies `f(x, y, z) = Fₙ`. -/
theorem initialWitnesses_checked :
    initialWitnesses.all (fun e => decide (f e.2.1 e.2.2.1 e.2.2.2 = (Nat.fastFib e.1 : ℤ))) =
      true := by
  decide +kernel

/-- Every index below 48 other than 8 has a witness, or its Fibonacci number
is eligible and not 7 or 10 modulo 12. -/
theorem initial_window_checked :
    (List.range 48).all (fun n => decide (n = 8 ∨ (∃ e ∈ initialWitnesses, e.1 = n) ∨
      (ResidualEligible (Nat.fastFib n) ∧ Nat.fastFib n % 12 ≠ 7 ∧
        Nat.fastFib n % 12 ≠ 10))) = true := by
  decide +kernel

/-- `f` represents `F₀, …, F₇`, by the vectors of `initialWitnesses`. This part
of Proposition 3.5 does not use Proposition 3.3. -/
theorem representsF_fib_of_lt_eight (n : ℕ) (hn : n < 8) : RepresentsF (Nat.fib n : ℤ) := by
  have hmem : ∃ e ∈ initialWitnesses, e.1 = n := by
    interval_cases n <;> decide
  obtain ⟨e, he, rfl⟩ := hmem
  have hw := List.all_eq_true.mp initialWitnesses_checked e he
  simp only [Nat.fastFib_eq, decide_eq_true_eq] at hw
  exact ⟨e.2.1, e.2.2.1, e.2.2.2, hw⟩

/-- `f` represents every Fibonacci number with index below 48 except
`F₈ = 21` (part of Proposition 3.5). -/
theorem representsF_fib_initial
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    (n : ℕ) (hn : n < 48) (h8 : n ≠ 8) : RepresentsF (Nat.fib n : ℤ) := by
  have hrow := List.all_eq_true.mp initial_window_checked n (List.mem_range.mpr hn)
  simp only [Nat.fastFib_eq, decide_eq_true_eq] at hrow
  rcases hrow with h | ⟨e, he, rfl⟩ | ⟨helig, h7, h10⟩
  · exact absurd h h8
  · have hw := List.all_eq_true.mp initialWitnesses_checked e he
    simp only [Nat.fastFib_eq, decide_eq_true_eq] at hw
    exact ⟨e.2.1, e.2.2.1, e.2.2.2, hw⟩
  · exact representsF_of_class_of_mod_twelve _ (hclass _ helig) (by omega) (by omega)

end FibonacciCriterion.Irregular
