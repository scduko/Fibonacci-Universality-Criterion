import FibonacciCriterion.Fibonacci.Period

/-!
# Fibonacci numbers modulo 2, 3, 5, 8, and 16

The ranks of apparition of 2, 3, and 5 are 3, 4, and 5 (`two_dvd_fib_iff`,
`three_dvd_fib_iff`, `five_dvd_fib_iff`); moreover `8 ∣ Fₙ` if and only if
`6 ∣ n`, and `Fₙ` is never 10 or 14 modulo 16. Each fact is checked over one
return time of the Fibonacci state and extended to every index by
`fib_mod_reduce_index`.
-/

namespace FibonacciCriterion

/-- Return times of the Fibonacci state: 3 modulo 2, 8 modulo 3, 20 modulo 5,
and 24 modulo 16. -/
theorem fib_state_returns_two_three_five_sixteen :
    FibStateReturns 2 3 ∧ FibStateReturns 3 8 ∧
      FibStateReturns 5 20 ∧ FibStateReturns 16 24 := by
  unfold FibStateReturns
  decide

/-- `2 ∣ Fₙ` if and only if `3 ∣ n`, including `n = 0`: the rank of apparition
of 2 is 3. -/
theorem two_dvd_fib_iff (n : ℕ) : 2 ∣ Nat.fib n ↔ 3 ∣ n := by
  have hfinite : ∀ r : Fin 3, Nat.fib r.val % 2 = 0 ↔ r.val = 0 := by decide
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    fib_mod_reduce_index 2 3 fib_state_returns_two_three_five_sixteen.1 n]
  exact hfinite ⟨n % 3, Nat.mod_lt n (by decide)⟩

/-- `3 ∣ Fₙ` if and only if `4 ∣ n`: the rank of apparition of 3 is 4. -/
theorem three_dvd_fib_iff (n : ℕ) : 3 ∣ Nat.fib n ↔ 4 ∣ n := by
  have hfinite : ∀ r : Fin 8, Nat.fib r.val % 3 = 0 ↔ r.val % 4 = 0 := by decide
  have hr := hfinite ⟨n % 8, Nat.mod_lt n (by decide)⟩
  change Nat.fib (n % 8) % 3 = 0 ↔ (n % 8) % 4 = 0 at hr
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    fib_mod_reduce_index 3 8 fib_state_returns_two_three_five_sixteen.2.1 n]
  simpa only [Nat.mod_mod_of_dvd n (by decide : 4 ∣ 8)] using hr

/-- `5 ∣ Fₙ` if and only if `5 ∣ n`: the rank of apparition of 5 is 5. -/
theorem five_dvd_fib_iff (n : ℕ) : 5 ∣ Nat.fib n ↔ 5 ∣ n := by
  have hfinite : ∀ r : Fin 20, Nat.fib r.val % 5 = 0 ↔ r.val % 5 = 0 := by decide
  have hr := hfinite ⟨n % 20, Nat.mod_lt n (by decide)⟩
  change Nat.fib (n % 20) % 5 = 0 ↔ (n % 20) % 5 = 0 at hr
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    fib_mod_reduce_index 5 20 fib_state_returns_two_three_five_sixteen.2.2.1 n]
  simpa only [Nat.mod_mod_of_dvd n (by decide : 5 ∣ 20)] using hr

/-- `8 ∣ Fₙ` if and only if `6 ∣ n`. -/
theorem eight_dvd_fib_iff (n : ℕ) : 8 ∣ Nat.fib n ↔ 6 ∣ n := by
  have hfinite : ∀ r : Fin 12, Nat.fib r.val % 8 = 0 ↔ r.val % 6 = 0 := by decide
  have hr := hfinite ⟨n % 12, Nat.mod_lt n (by decide)⟩
  change Nat.fib (n % 12) % 8 = 0 ↔ (n % 12) % 6 = 0 at hr
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    fib_mod_reduce_index 8 12 fib_state_returns_eight n]
  simpa only [Nat.mod_mod_of_dvd n (by decide : 6 ∣ 12)] using hr

/-- No Fibonacci number is 14 modulo 16. Equivalently, if `v₂(Fₙ) = 1`, then
`u₂(Fₙ) ≢ 7 (mod 8)`. -/
theorem fib_mod_sixteen_ne_fourteen (n : ℕ) : Nat.fib n % 16 ≠ 14 := by
  have hfinite : ∀ r : Fin 24, Nat.fib r.val % 16 ≠ 14 := by decide
  rw [fib_mod_reduce_index 16 24 fib_state_returns_two_three_five_sixteen.2.2.2 n]
  exact hfinite ⟨n % 24, Nat.mod_lt n (by decide)⟩

/-- No Fibonacci number is 10 modulo 16. Equivalently, if `v₂(Fₙ) = 1`, then
`u₂(Fₙ) ≢ 5 (mod 8)`. -/
theorem fib_mod_sixteen_ne_ten (n : ℕ) : Nat.fib n % 16 ≠ 10 := by
  have hfinite : ∀ r : Fin 24, Nat.fib r.val % 16 ≠ 10 := by decide
  rw [fib_mod_reduce_index 16 24 fib_state_returns_two_three_five_sixteen.2.2.2 n]
  exact hfinite ⟨n % 24, Nat.mod_lt n (by decide)⟩

end FibonacciCriterion
