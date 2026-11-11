import FibonacciCriterion.Fibonacci.SmallModuli
import FibonacciCriterion.Arithmetic.PrimePowerNormalization

/-!
# The Fibonacci valuation formulas and the bounds (1)

`FibonacciValuationInputs` states the valuation formulas of Lemma 2.2 at 2, 3,
and 5 as factorizations `Fₙ = p^a u` with `p ∤ u`, so no valuation function
is needed. From them this file derives the bounds (1)
(`two_prime_power_bound`, `three_prime_power_bound`, `five_prime_power_bound`)
and the fact that `v₂(Fₙ) ≠ 2` (`two_even_exponent_zero_or_four_le`). It also
restates the residues modulo 16 of `Fibonacci.SmallModuli` for the odd part of
a Fibonacci number of valuation 1 (`two_unit_not_seven_of_exponent_one`,
`two_unit_not_five_of_exponent_one`); these two lemmas do not use the formulas.
The criterion proof takes the formulas as a hypothesis; `Fibonacci.Valuations`
proves them.
-/

namespace FibonacciCriterion

/-- The valuation formulas of Lemma 2.2 at 2, 3, and 5, stated as
factorizations with a unit part, for `n ≥ 1`. `two_exact` lists the three
cases `v₂(Fₙ) = 0` for `3 ∤ n`, `v₂(Fₙ) = 1` for `n ≡ 3 (mod 6)`, and
`v₂(Fₙ) = v₂(n) + 2` for `6 ∣ n`; `three_exact` encodes `v₃(Fₙ) = 1 + v₃(n)`
for `4 ∣ n` and `v₃(Fₙ) = 0` otherwise; `five_exact` encodes
`v₅(Fₙ) = v₅(n)`. -/
structure FibonacciValuationInputs : Prop where
  two_exact : ∀ n : ℕ, 1 ≤ n →
    (¬ 3 ∣ n ∧ ∃ u : ℕ, Nat.fib n = u ∧ u % 2 = 1) ∨
    (n % 6 = 3 ∧ ∃ u : ℕ, Nat.fib n = 2 * u ∧ u % 2 = 1) ∨
    (6 ∣ n ∧ ∃ a m u : ℕ,
      n = 2 ^ a * m ∧ m % 2 = 1 ∧
      Nat.fib n = 2 ^ (a + 2) * u ∧ u % 2 = 1)
  three_exact : ∀ n : ℕ, 1 ≤ n →
    (¬ 4 ∣ n ∧ ∃ u : ℕ, Nat.fib n = u ∧ u % 3 ≠ 0) ∨
    (4 ∣ n ∧ ∃ a m u : ℕ,
      n = 3 ^ a * m ∧ m % 3 ≠ 0 ∧
      Nat.fib n = 3 ^ (a + 1) * u ∧ u % 3 ≠ 0)
  five_exact : ∀ n : ℕ, 1 ≤ n → ∃ a m u : ℕ,
    n = 5 ^ a * m ∧ m % 5 ≠ 0 ∧
    Nat.fib n = 5 ^ a * u ∧ u % 5 ≠ 0

namespace FibonacciValuationInputs

variable (vInputs : FibonacciValuationInputs)

/-- If `Fₙ = 2u`, then `u ≢ 7 (mod 8)`: a Fibonacci number of 2-adic
valuation 1 has odd part different from 7 modulo 8. The same statement fails
at higher odd valuations, first at `F₄₂`. -/
theorem two_unit_not_seven_of_exponent_one (n : ℕ) (u : ℤ)
    (hfac : (Nat.fib n : ℤ) = 2 * u) : u % 8 ≠ 7 := by
  intro hu
  apply fib_mod_sixteen_ne_fourteen n
  have hmod := congrArg (fun z : ℤ => z % 16) hfac
  have hz : (Nat.fib n : ℤ) % 16 = 14 := by omega
  exact_mod_cast hz

/-- If `Fₙ = 2u`, then `u ≢ 5 (mod 8)`: a Fibonacci number of 2-adic
valuation 1 has odd part different from 5 modulo 8. -/
theorem two_unit_not_five_of_exponent_one (n : ℕ) (u : ℤ)
    (hfac : (Nat.fib n : ℤ) = 2 * u) : u % 8 ≠ 5 := by
  intro hu
  apply fib_mod_sixteen_ne_ten n
  have hmod := congrArg (fun z : ℤ => z % 16) hfac
  have hz : (Nat.fib n : ℤ) % 16 = 10 := by omega
  exact_mod_cast hz

include vInputs

/-- The bound (1) at 2: for `n ≥ 1`, `Fₙ = 2^a u` with `u` odd and
`2^a ≤ 4n`. -/
theorem two_prime_power_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ a u : ℕ, Nat.fib n = 2 ^ a * u ∧ u % 2 = 1 ∧ 2 ^ a ≤ 4 * n := by
  rcases FibonacciValuationInputs.two_exact vInputs n hn with ⟨-, u, hu, hu2⟩ |
      ⟨-, u, hu, hu2⟩ | ⟨-, a, m, u, hnfac, hm2, hufac, hu2⟩
  · exact ⟨0, u, by simpa using hu, hu2, by omega⟩
  · exact ⟨1, u, by simpa using hu, hu2, by omega⟩
  · refine ⟨a + 2, u, hufac, hu2, ?_⟩
    have hm : 1 ≤ m := by omega
    rw [hnfac]
    rw [pow_add]
    norm_num
    nlinarith [Nat.zero_le (2 ^ a)]

/-- The bound (1) at 3: for `n ≥ 1`, `Fₙ = 3^a u` with `3 ∤ u` and
`3^a ≤ 3n`. -/
theorem three_prime_power_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ a u : ℕ, Nat.fib n = 3 ^ a * u ∧ u % 3 ≠ 0 ∧ 3 ^ a ≤ 3 * n := by
  rcases FibonacciValuationInputs.three_exact vInputs n hn with ⟨-, u, hu, hu3⟩ |
      ⟨-, a, m, u, hnfac, hm3, hufac, hu3⟩
  · exact ⟨0, u, by simpa using hu, hu3, by omega⟩
  · refine ⟨a + 1, u, hufac, hu3, ?_⟩
    have hm : 1 ≤ m := by omega
    rw [hnfac, pow_add]
    norm_num
    nlinarith [Nat.zero_le (3 ^ a)]

/-- The bound (1) at 5: for `n ≥ 1`, `Fₙ = 5^a u` with `5 ∤ u` and
`5^a ≤ n`. -/
theorem five_prime_power_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ a u : ℕ, Nat.fib n = 5 ^ a * u ∧ u % 5 ≠ 0 ∧ 5 ^ a ≤ n := by
  obtain ⟨a, m, u, hnfac, hm5, hufac, hu5⟩ :=
    FibonacciValuationInputs.five_exact vInputs n hn
  refine ⟨a, u, hufac, hu5, ?_⟩
  have hm : 1 ≤ m := by omega
  rw [hnfac]
  nlinarith [Nat.zero_le (5 ^ a)]

/-- If `n ≥ 1` and `Fₙ = 2^a u` with `u` odd and `a` even, then `a = 0` or
`a ≥ 4`. This rules out valuation 2 in the proof of Proposition 5.7 for
`⟨1,2,2⟩`. -/
theorem two_even_exponent_zero_or_four_le (n a u : ℕ) (hn : 1 ≤ n)
    (hfac : Nat.fib n = 2 ^ a * u) (hu : u % 2 = 1)
    (heven : a % 2 = 0) : a = 0 ∨ 4 ≤ a := by
  rcases FibonacciValuationInputs.two_exact vInputs n hn with ⟨-, v, hv, hv2⟩ |
      ⟨-, v, hv, hv2⟩ | ⟨h6, b, m, v, hnfac, hm2, hv, hv2⟩
  · left
    have hu' : (u : ℤ) % 2 ≠ 0 := by exact_mod_cast (show u % 2 ≠ 0 by omega)
    have hv' : (v : ℤ) % 2 ≠ 0 := by exact_mod_cast (show v % 2 ≠ 0 by omega)
    have heq0 : (2 : ℤ) ^ a * (u : ℤ) = (v : ℤ) := by
      exact_mod_cast (hfac.symm.trans hv)
    have heq : (2 : ℤ) ^ a * u = 2 ^ 0 * v := by
      simpa using heq0
    exact pow_mul_unit_exponent_unique 2 (by norm_num) hu' hv' heq
  · have hu' : (u : ℤ) % 2 ≠ 0 := by exact_mod_cast (show u % 2 ≠ 0 by omega)
    have hv' : (v : ℤ) % 2 ≠ 0 := by exact_mod_cast (show v % 2 ≠ 0 by omega)
    have heq0 : (2 : ℤ) ^ a * (u : ℤ) = 2 * (v : ℤ) := by
      exact_mod_cast (hfac.symm.trans hv)
    have heq : (2 : ℤ) ^ a * (u : ℤ) = 2 ^ 1 * (v : ℤ) := by
      simpa using heq0
    have ha : a = 1 :=
      pow_mul_unit_exponent_unique 2 (by norm_num) hu' hv' heq
    omega
  · have hu' : (u : ℤ) % 2 ≠ 0 := by exact_mod_cast (show u % 2 ≠ 0 by omega)
    have hv' : (v : ℤ) % 2 ≠ 0 := by exact_mod_cast (show v % 2 ≠ 0 by omega)
    have heq : (2 : ℤ) ^ a * (u : ℤ) = 2 ^ (b + 2) * (v : ℤ) := by
      exact_mod_cast (hfac.symm.trans hv)
    have ha : a = b + 2 :=
      pow_mul_unit_exponent_unique 2 (by norm_num) hu' hv' heq
    have hb : 1 ≤ b := by
      by_contra h
      have hb0 : b = 0 := by omega
      subst b
      simp only [pow_zero, one_mul] at hnfac
      obtain ⟨k, hk⟩ := h6
      omega
    omega

end FibonacciValuationInputs

end FibonacciCriterion
