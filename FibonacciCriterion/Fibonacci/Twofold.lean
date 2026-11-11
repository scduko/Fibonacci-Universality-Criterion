import FibonacciCriterion.Fibonacci.Addition
import FibonacciCriterion.Fibonacci.SmallModuli

/-!
# Multiplying the Fibonacci index by 2

The doubling identity `F₂ₘ = Fₘ (2Fₘ₊₁ - Fₘ)` gives the case `6 ∣ n` of the
valuation formula at 2 (Lemma 2.2). For odd `m` divisible by 3, `F₂ₘ` has
valuation 3, by the divisibility criteria modulo 8 and 16
(`fib_two_base_unit`). Once `8 ∣ Fₘ`, each further doubling raises the
valuation by 1 (`fib_two_mul_lift_unit`), so `F_{2^{r+1} m}` has valuation
`r + 3` (`fib_two_succ_pow_mul_unit`).
-/

namespace FibonacciCriterion

/-- `4 ∣ Fₙ` if and only if `6 ∣ n`. -/
theorem four_dvd_fib_iff (n : ℕ) : 4 ∣ Nat.fib n ↔ 6 ∣ n := by
  have hreturn : FibStateReturns 4 6 := by
    unfold FibStateReturns
    decide
  have hfinite : ∀ r : Fin 6,
      Nat.fib r.val % 4 = 0 ↔ r.val = 0 := by decide
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    fib_mod_reduce_index 4 6 hreturn n]
  exact hfinite ⟨n % 6, Nat.mod_lt n (by decide)⟩

/-- `16 ∣ Fₙ` if and only if `12 ∣ n`. -/
theorem sixteen_dvd_fib_iff (n : ℕ) : 16 ∣ Nat.fib n ↔ 12 ∣ n := by
  have hfinite : ∀ r : Fin 24,
      Nat.fib r.val % 16 = 0 ↔ r.val % 12 = 0 := by decide
  have hr := hfinite ⟨n % 24, Nat.mod_lt n (by decide)⟩
  change Nat.fib (n % 24) % 16 = 0 ↔ (n % 24) % 12 = 0 at hr
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    fib_mod_reduce_index 16 24
      fib_state_returns_two_three_five_sixteen.2.2.2 n]
  simpa only [Nat.mod_mod_of_dvd n (by decide : 12 ∣ 24)] using hr

/-- The doubling identity `F₂ₘ = Fₘ (2Fₘ₊₁ - Fₘ)` over `ℤ`. -/
theorem fib_two_mul_int (m : ℕ) :
    (Nat.fib (2 * m) : ℤ) =
      (Nat.fib m : ℤ) * (2 * Nat.fib (m + 1) - Nat.fib m) := by
  have h := fib_add_int m m
  have hi : m + m = 2 * m := by omega
  rw [hi] at h
  rw [h]
  ring

/-- If `8 ∣ Fₘ`, then `F₂ₘ = 2 Fₘ u` with `u ≡ Fₘ₊₁ (mod 2)`. -/
theorem fib_two_mul_factor (m : ℕ) (hm : (8 : ℤ) ∣ (Nat.fib m : ℤ)) :
    ∃ u : ℤ, (Nat.fib (2 * m) : ℤ) = 2 * (Nat.fib m : ℤ) * u ∧
      u % 2 = (Nat.fib (m + 1) : ℤ) % 2 := by
  obtain ⟨t, ht⟩ := hm
  refine ⟨(Nat.fib (m + 1) : ℤ) - 4 * t, ?_, ?_⟩
  · rw [fib_two_mul_int, ht]
    ring
  · simp [Int.sub_emod, Int.mul_emod]

/-- If `8 ∣ Fₘ`, then `F₂ₘ = 2 Fₘ u` with `u` odd. -/
theorem fib_two_mul_factor_unit (m : ℕ) (hm : (8 : ℤ) ∣ (Nat.fib m : ℤ)) :
    ∃ u : ℤ, (Nat.fib (2 * m) : ℤ) = 2 * (Nat.fib m : ℤ) * u ∧
      ¬(2 : ℤ) ∣ u := by
  obtain ⟨u, hu, hres⟩ := fib_two_mul_factor m hm
  refine ⟨u, hu, ?_⟩
  intro hdiv
  have hz : u % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp hdiv
  have hnextEven : (2 : ℤ) ∣ (Nat.fib (m + 1) : ℤ) :=
    Int.dvd_iff_emod_eq_zero.mpr (hres.symm.trans hz)
  have hmEven : 2 ∣ Nat.fib m := by
    have hm8 : 8 ∣ Nat.fib m := by exact_mod_cast hm
    exact (by norm_num : 2 ∣ 8).trans hm8
  have hnextEvenNat : 2 ∣ Nat.fib (m + 1) := by exact_mod_cast hnextEven
  have hd := Nat.dvd_gcd hmEven hnextEvenNat
  rw [(Nat.fib_coprime_fib_succ m).gcd_eq_one] at hd
  norm_num at hd

/-- If `Fₘ = 2^a u` with `u` odd and `a ≥ 3`, then `F₂ₘ = 2^{a+1} v` with `v`
odd. -/
theorem fib_two_mul_lift_unit (m a : ℕ) (u : ℤ)
    (hfac : (Nat.fib m : ℤ) = (2 : ℤ) ^ a * u)
    (ha : 3 ≤ a) (hunit : ¬(2 : ℤ) ∣ u) :
    ∃ v : ℤ, (Nat.fib (2 * m) : ℤ) = (2 : ℤ) ^ (a + 1) * v ∧
      ¬(2 : ℤ) ∣ v := by
  have hm : (8 : ℤ) ∣ (Nat.fib m : ℤ) := by
    refine ⟨(2 : ℤ) ^ (a - 3) * u, ?_⟩
    rw [hfac, show a = (a - 3) + 3 by omega, pow_add]
    norm_num
    ring
  obtain ⟨w, hw, hwunit⟩ := fib_two_mul_factor_unit m hm
  refine ⟨u * w, ?_, ?_⟩
  · rw [hw, hfac, pow_succ]
    ring
  · intro hd
    rcases (show Prime (2 : ℤ) by norm_num).dvd_mul.mp hd with hu | hw'
    · exact hunit hu
    · exact hwunit hw'

/-- If `m` is odd and divisible by 3, then `F₂ₘ = 2³ u` with `u` odd. -/
theorem fib_two_base_unit (m : ℕ) (h3 : 3 ∣ m) (hodd : m % 2 = 1) :
    ∃ u : ℤ, (Nat.fib (2 * m) : ℤ) = (2 : ℤ) ^ 3 * u ∧
      ¬(2 : ℤ) ∣ u := by
  have h6 : 6 ∣ 2 * m := by
    obtain ⟨k, rfl⟩ := h3
    exact ⟨k, by ring⟩
  have h8 : 8 ∣ Nat.fib (2 * m) := (eight_dvd_fib_iff (2 * m)).2 h6
  have h12 : ¬12 ∣ 2 * m := by
    intro hd
    obtain ⟨k, hk⟩ := hd
    have : m % 2 = 0 := by omega
    omega
  have h16 : ¬16 ∣ Nat.fib (2 * m) := by
    intro hd
    exact h12 ((sixteen_dvd_fib_iff (2 * m)).1 hd)
  obtain ⟨u, hu⟩ := h8
  refine ⟨u, ?_, ?_⟩
  · have hu' : Nat.fib (2 * m) = 8 * u := hu
    norm_num at hu' ⊢
    exact_mod_cast hu'
  · intro hu2
    have hu2Nat : 2 ∣ u := by exact_mod_cast hu2
    apply h16
    obtain ⟨v, rfl⟩ := hu2Nat
    refine ⟨v, ?_⟩
    rw [hu]
    ring

/-- If `m` is odd and divisible by 3, then `F_{2^{r+1} m} = 2^{r+3} u` with `u`
odd. -/
theorem fib_two_succ_pow_mul_unit (r m : ℕ) (h3 : 3 ∣ m) (hodd : m % 2 = 1) :
    ∃ u : ℤ, (Nat.fib (2 ^ (r + 1) * m) : ℤ) =
      (2 : ℤ) ^ (r + 3) * u ∧ ¬(2 : ℤ) ∣ u := by
  induction r with
  | zero =>
      simpa using fib_two_base_unit m h3 hodd
  | succ r ih =>
      obtain ⟨u, hu, hunit⟩ := ih
      obtain ⟨v, hv, hvunit⟩ :=
        fib_two_mul_lift_unit (2 ^ (r + 1) * m) (r + 3) u hu (by omega) hunit
      refine ⟨v, ?_, hvunit⟩
      have hi : 2 ^ (r.succ + 1) * m = 2 * (2 ^ (r + 1) * m) := by
        rw [show r.succ + 1 = (r + 1) + 1 by omega, pow_succ]
        ring
      rw [hi, hv]

end FibonacciCriterion
