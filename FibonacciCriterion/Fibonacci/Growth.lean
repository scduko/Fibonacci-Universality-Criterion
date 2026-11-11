import Mathlib

/-!
# Monotonicity of `Fₙ / n` (Lemma 2.1)

The sequence `Fₙ / n` is strictly increasing for `n ≥ 2` (`fib_succ_mul_gt`,
for consecutive indices). The proof of the criterion uses the consequence
`Fₘ / m ≤ Fₙ / n` for `2 ≤ m ≤ n` (`fib_mul_le_of_le`). Both are stated without
division. With the bounds (1) of §2, `p^{v_p(Fₙ)} ≤ c n`, the value
`Fₘ / (c m)` at one index `m` is a lower bound for the unit part `u_p(Fₙ)` at
every index `n ≥ m`.
-/

namespace FibonacciCriterion

/-- Lemma 2.1 for consecutive indices: `n Fₙ₊₁ > (n + 1) Fₙ` for `n ≥ 2`. -/
theorem fib_succ_mul_gt (n : ℕ) (hn : 2 ≤ n) :
    (n + 1) * Nat.fib n < n * Nat.fib (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  -- `n Fₙ₊₁ - (n + 1) Fₙ = n Fₙ₋₁ - Fₙ`; this is 1 for `n = 2`, and for
  -- `n ≥ 3`, `Fₙ ≤ 2 Fₙ₋₁ < n Fₙ₋₁`.
  have h3 : Nat.fib (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 1) := by
    rw [Nat.fib_add_two]
    ring
  have h2 : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := by
    rw [Nat.fib_add_two]
    ring
  have hmono : Nat.fib k ≤ Nat.fib (k + 1) := Nat.fib_mono (Nat.le_succ k)
  have hpos : 0 < Nat.fib (k + 1) := Nat.fib_pos.2 (Nat.succ_pos k)
  have hlt : Nat.fib k < (k + 1) * Nat.fib (k + 1) := by
    rcases k with _ | k
    · simp
    · nlinarith
  rw [show k + 2 + 1 = k + 3 by ring, h3, h2]
  nlinarith

/-- Lemma 2.1: for `2 ≤ m ≤ n`, `Fₘ / m ≤ Fₙ / n`, stated as `Fₘ n ≤ Fₙ m`. -/
theorem fib_mul_le_of_le {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    Nat.fib m * n ≤ Nat.fib n * m := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ n hmn ih =>
      have hstep := fib_succ_mul_gt n (hm.trans hmn)
      have hn : 0 < n := by omega
      -- `Fₘ (n + 1) n ≤ Fₙ m (n + 1) < Fₙ₊₁ m n`.
      have h1 : Nat.fib m * (n + 1) * n ≤ Nat.fib (n + 1) * m * n := by
        calc Nat.fib m * (n + 1) * n = Nat.fib m * n * (n + 1) := by ring
          _ ≤ Nat.fib n * m * (n + 1) := Nat.mul_le_mul_right _ ih
          _ = m * ((n + 1) * Nat.fib n) := by ring
          _ ≤ m * (n * Nat.fib (n + 1)) := Nat.mul_le_mul_left _ hstep.le
          _ = Nat.fib (n + 1) * m * n := by ring
      exact Nat.le_of_mul_le_mul_right h1 hn

end FibonacciCriterion
