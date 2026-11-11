import Mathlib

/-!
# Fibonacci residues from a return of the state

If the state `(F_T, F_{T+1})` is `(0, 1)` modulo `m`, then `T` is a period of
the Fibonacci residues modulo `m` (`fib_mod_add_period`), and `Fₙ mod m`
depends only on `n mod T` (`fib_mod_reduce_index`). A finite table over one
period then gives a statement about every index. The manuscript's Lemma 2.3
lists least periods; here `T` need not be the least period. The file ends with
the returns modulo 8 and 9 (`fib_state_returns_eight`,
`fib_state_returns_nine`); `Fibonacci.SmallModuli` and `Fibonacci.Twofold` have
those for 2, 3, 4, 5, and 16.
-/

namespace FibonacciCriterion

/-- `T` is a return time modulo `m`: the state `(F_T, F_{T+1})` is `(0, 1)`
modulo `m`. -/
def FibStateReturns (m T : ℕ) : Prop :=
  Nat.fib T % m = 0 ∧ Nat.fib (T + 1) % m = 1 % m

/-- If the state returns at `T`, then the states at `n + T` and at `n` agree
modulo `m`. -/
theorem fib_mod_state_period (m T : ℕ) (h : FibStateReturns m T) (n : ℕ) :
    Nat.fib (n + T) % m = Nat.fib n % m ∧
      Nat.fib (n + T + 1) % m = Nat.fib (n + 1) % m := by
  induction n with
  | zero =>
      simpa only [FibStateReturns, Nat.zero_add, Nat.fib_zero, Nat.zero_mod, Nat.fib_one] using h
  | succ n ih =>
      have hindex : n.succ + T = n + T + 1 := by omega
      rw [hindex]
      constructor
      · exact ih.2
      · change Nat.fib (n + T + 2) % m = Nat.fib (n + 2) % m
        rw [Nat.fib_add_two, Nat.fib_add_two]
        calc
          (Nat.fib (n + T) + Nat.fib (n + T + 1)) % m =
              (Nat.fib (n + T) % m + Nat.fib (n + T + 1) % m) % m :=
            Nat.add_mod _ _ _
          _ = (Nat.fib n % m + Nat.fib (n + 1) % m) % m := by rw [ih.1, ih.2]
          _ = (Nat.fib n + Nat.fib (n + 1)) % m := (Nat.add_mod _ _ _).symm

/-- A return time is a period of the Fibonacci residues modulo `m`. -/
theorem fib_mod_add_period (m T : ℕ) (h : FibStateReturns m T) (n : ℕ) :
    Nat.fib (n + T) % m = Nat.fib n % m :=
  (fib_mod_state_period m T h n).1

/-- Adding a multiple of a return time to the index preserves the residue. -/
theorem fib_mod_add_mul_period (m T : ℕ) (h : FibStateReturns m T) (n k : ℕ) :
    Nat.fib (n + k * T) % m = Nat.fib n % m := by
  induction k with
  | zero => simp
  | succ k ih =>
      simpa only [Nat.succ_mul, ← Nat.add_assoc] using
        (fib_mod_add_period m T h (n + k * T)).trans ih

/-- `Fₙ mod m` depends only on `n` modulo a return time `T`. -/
theorem fib_mod_reduce_index (m T : ℕ) (h : FibStateReturns m T) (n : ℕ) :
    Nat.fib n % m = Nat.fib (n % T) % m := by
  calc
    Nat.fib n % m = Nat.fib (n % T + (n / T) * T) % m := by
      rw [Nat.mul_comm (n / T) T, Nat.mod_add_div]
    _ = Nat.fib (n % T) % m := fib_mod_add_mul_period m T h (n % T) (n / T)

/-- The Fibonacci state returns to `(0, 1)` modulo 8 at index 12. -/
theorem fib_state_returns_eight : FibStateReturns 8 12 := by
  unfold FibStateReturns
  decide

/-- The Fibonacci state returns to `(0, 1)` modulo 9 at index 24. -/
theorem fib_state_returns_nine : FibStateReturns 9 24 := by
  unfold FibStateReturns
  decide

end FibonacciCriterion
