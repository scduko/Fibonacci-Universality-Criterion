import Mathlib

/-!
# The Fibonacci addition formula over the integers

Two forms of the addition formula over `ℤ`: `fib_add_int`, which avoids
predecessor indices, and `fib_add_succ_int`. The identities for `F₂ₘ`, `F₃ₘ`,
and `F₅ₘ` behind the valuation formulas at 2, 3, and 5 (Lemma 2.2) are
derived from them.
-/

namespace FibonacciCriterion

/-- The addition formula without predecessor indices:
`Fₘ₊ₙ = Fₘ Fₙ₊₁ + (Fₘ₊₁ - Fₘ) Fₙ` over `ℤ`. -/
theorem fib_add_int (m n : ℕ) :
    (Nat.fib (m + n) : ℤ) =
      (Nat.fib m : ℤ) * Nat.fib (n + 1) +
        ((Nat.fib (m + 1) : ℤ) - Nat.fib m) * Nat.fib n := by
  cases n with
  | zero => simp
  | succ n =>
    have hi : m + n.succ = m + n + 1 := by omega
    have hr : (Nat.fib (n.succ + 1) : ℤ) =
        (Nat.fib n : ℤ) + Nat.fib (n + 1) := by
      exact_mod_cast (@Nat.fib_add_two n)
    rw [hi, Nat.fib_add]
    push_cast
    rw [hr]
    change _ = (Nat.fib m : ℤ) * _ + _ * Nat.fib (n + 1)
    ring

/-- The addition formula at the next index: `Fₘ₊ₙ₊₁ = Fₘ Fₙ + Fₘ₊₁ Fₙ₊₁` over
`ℤ`. -/
theorem fib_add_succ_int (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ) =
      (Nat.fib m : ℤ) * Nat.fib n +
        (Nat.fib (m + 1) : ℤ) * Nat.fib (n + 1) := by
  exact_mod_cast Nat.fib_add m n

end FibonacciCriterion
