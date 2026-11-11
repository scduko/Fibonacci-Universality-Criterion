import Mathlib

/-!
# Factorizations by a power of a fixed base

The statements of this library write an integer as `p^a u` with `p ∤ u`
instead of using a valuation function. Every nonzero integer has such a factorization
(`exists_pow_mul_not_dvd`), and its exponent is unique
(`pow_mul_unit_exponent_unique`). Primality of `p` is not needed for
uniqueness: `p ≥ 2` suffices once both unit parts are nonzero modulo `p`.
-/

namespace FibonacciCriterion

/-- For `p ≥ 2`, if `p^a u = p^b v` with `u` and `v` nonzero modulo `p`, then
`a = b`. -/
theorem pow_mul_unit_exponent_unique (p : ℤ) (hp : 2 ≤ p)
    {a b : ℕ} {u v : ℤ} (hu : u % p ≠ 0) (hv : v % p ≠ 0)
    (h : p ^ a * u = p ^ b * v) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · let d := b - a
    have hd : 0 < d := by simp [d, hab]
    have hb : b = a + d := by omega
    have hp0 : p ^ a ≠ 0 := pow_ne_zero _ (by omega)
    have huv : u = p ^ d * v := by
      apply mul_left_cancel₀ hp0
      simpa [hb, pow_add, mul_assoc] using h
    obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    exfalso
    apply hu
    rw [huv, hc, pow_succ, Int.mul_emod]
    simp
  · exact hab
  · let d := a - b
    have hd : 0 < d := by simp [d, hab]
    have ha : a = b + d := by omega
    have hp0 : p ^ b ≠ 0 := pow_ne_zero _ (by omega)
    have hvu : v = p ^ d * u := by
      apply mul_left_cancel₀ hp0
      simpa [ha, pow_add, mul_assoc] using h.symm
    obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    exfalso
    apply hv
    rw [hvu, hc, pow_succ, Int.mul_emod]
    simp

/-- The factorization `2^a u` with `u` odd is unique. -/
theorem pow_two_odd_unique {a b : ℕ} {u v : ℤ} (hu : u % 2 = 1) (hv : v % 2 = 1)
    (h : (2 : ℤ) ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have hab := pow_mul_unit_exponent_unique 2 le_rfl (by omega) (by omega) h
  subst hab
  exact ⟨rfl, mul_left_cancel₀ (by positivity) h⟩

/-- Every nonzero integer is a power of a base `p ≠ 1` times an integer not
divisible by `p`. -/
theorem exists_pow_mul_not_dvd (p : ℕ) (hp : p ≠ 1) (k : ℤ) (hk : k ≠ 0) :
    ∃ (s : ℕ) (ω : ℤ), k = (p : ℤ) ^ s * ω ∧ ¬ (p : ℤ) ∣ ω := by
  obtain ⟨s, n, hn, hfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hk) p hp
  rcases Int.natAbs_eq k with h | h
  · refine ⟨s, n, ?_, ?_⟩
    · rw [h, hfac]
      push_cast
      ring
    · exact_mod_cast hn
  · refine ⟨s, -(n : ℤ), ?_, ?_⟩
    · rw [h, hfac]
      push_cast
      ring
    · rw [dvd_neg]
      exact_mod_cast hn

/-- If `q > 0` and `2^k ∤ q`, then `q = 2^s ω` with `ω` odd and `s < k`. -/
theorem exists_twoAdic_normalization_lt (q : ℤ) (hq : 0 < q) (k : ℕ)
    (hk : q % 2 ^ k ≠ 0) :
    ∃ (s : ℕ) (ω : ℤ), q = 2 ^ s * ω ∧ ω % 2 = 1 ∧ s < k := by
  obtain ⟨s, ω, hfac, hω⟩ := exists_pow_mul_not_dvd 2 (by norm_num) q hq.ne'
  push_cast at hfac hω
  refine ⟨s, ω, hfac, by omega, ?_⟩
  by_contra hs
  apply hk
  rw [hfac, show s = k + (s - k) by omega, pow_add, mul_assoc]
  exact Int.mul_emod_right _ _

end FibonacciCriterion
