import FibonacciCriterion.Fibonacci.Addition
import FibonacciCriterion.Fibonacci.SmallModuli

/-!
# Multiplying the Fibonacci index by 3

The tripling identity `F₃ₘ = 3Fₘ Fₘ₊₁² - 3Fₘ² Fₘ₊₁ + 2Fₘ³` gives the valuation
formula at 3 (Lemma 2.2). If `3 ∣ Fₘ`, then `F₃ₘ` has one more factor of 3
than `Fₘ` (`fib_three_mul_lift_unit`). For `4 ∣ m` and `3 ∤ m`, `Fₘ` has
valuation 1, by the divisibility criteria modulo 3 and 9
(`fib_three_base_unit`), so `F_{3^a m}` has valuation `a + 1`
(`fib_three_pow_mul_unit`).
-/

namespace FibonacciCriterion

/-- The tripling identity `F₃ₘ = 3Fₘ Fₘ₊₁² - 3Fₘ² Fₘ₊₁ + 2Fₘ³` over `ℤ`. -/
theorem fib_three_mul_int (m : ℕ) :
    (Nat.fib (3 * m) : ℤ) =
      3 * (Nat.fib m : ℤ) * (Nat.fib (m + 1) : ℤ) ^ 2 -
      3 * (Nat.fib m : ℤ) ^ 2 * Nat.fib (m + 1) +
      2 * (Nat.fib m : ℤ) ^ 3 := by
  have hi2 : m + m = 2 * m := by omega
  have h2 := fib_add_int m m
  rw [hi2] at h2
  have h2s := fib_add_succ_int m m
  rw [hi2] at h2s
  have hi3 : 2 * m + m = 3 * m := by omega
  have h3 := fib_add_int (2 * m) m
  rw [hi3] at h3
  simp only [h3, h2, h2s]
  ring

/-- The cofactor `y² - 3ty + 6t²` of `3Fₘ` in `F₃ₘ`, where `Fₘ = 3t` and
`y = Fₘ₊₁`. -/
def threefoldUnit (t y : ℤ) : ℤ := y ^ 2 - 3 * t * y + 6 * t ^ 2

/-- If `3 ∣ Fₘ`, then `F₃ₘ = 3 Fₘ u` with `u ≡ Fₘ₊₁² (mod 3)`. -/
theorem fib_three_mul_factor (m : ℕ) (hm : (3 : ℤ) ∣ (Nat.fib m : ℤ)) :
    ∃ u : ℤ, (Nat.fib (3 * m) : ℤ) = 3 * (Nat.fib m : ℤ) * u ∧
      u % 3 = (Nat.fib (m + 1) : ℤ) ^ 2 % 3 := by
  obtain ⟨t, ht⟩ := hm
  refine ⟨threefoldUnit t (Nat.fib (m + 1)), ?_, ?_⟩
  · rw [fib_three_mul_int, ht]
    unfold threefoldUnit
    ring
  · simp [threefoldUnit, Int.add_emod, Int.sub_emod, Int.mul_emod]

/-- If `3 ∣ Fₘ`, then `3 ∤ Fₘ₊₁`. -/
theorem three_not_dvd_fib_succ (m : ℕ) (hm : 3 ∣ Nat.fib m) :
    ¬3 ∣ Nat.fib (m + 1) := by
  intro hnext
  have hd := Nat.dvd_gcd hm hnext
  rw [(Nat.fib_coprime_fib_succ m).gcd_eq_one] at hd
  norm_num at hd

/-- If `3 ∣ Fₘ`, then `F₃ₘ = 3 Fₘ u` with `3 ∤ u`. -/
theorem fib_three_mul_factor_unit (m : ℕ)
    (hm : (3 : ℤ) ∣ (Nat.fib m : ℤ)) :
    ∃ u : ℤ, (Nat.fib (3 * m) : ℤ) = 3 * (Nat.fib m : ℤ) * u ∧
      ¬(3 : ℤ) ∣ u := by
  obtain ⟨u, hu, hres⟩ := fib_three_mul_factor m hm
  refine ⟨u, hu, ?_⟩
  intro hdiv
  have hz : u % 3 = 0 := Int.dvd_iff_emod_eq_zero.mp hdiv
  have hpow : (3 : ℤ) ∣ (Nat.fib (m + 1) : ℤ) ^ 2 :=
    Int.dvd_iff_emod_eq_zero.mpr (hres.symm.trans hz)
  have hnext : (3 : ℤ) ∣ (Nat.fib (m + 1) : ℤ) :=
    (show Prime (3 : ℤ) by norm_num).dvd_of_dvd_pow hpow
  have hmNat : 3 ∣ Nat.fib m := by exact_mod_cast hm
  have hnextNat : 3 ∣ Nat.fib (m + 1) := by exact_mod_cast hnext
  exact three_not_dvd_fib_succ m hmNat hnextNat

/-- If `Fₘ = 3^a u` with `a ≥ 1` and `3 ∤ u`, then `F₃ₘ = 3^{a+1} v` with
`3 ∤ v`. -/
theorem fib_three_mul_lift_unit (m a : ℕ) (u : ℤ)
    (hfac : (Nat.fib m : ℤ) = (3 : ℤ) ^ a * u)
    (ha : 1 ≤ a) (hunit : ¬(3 : ℤ) ∣ u) :
    ∃ v : ℤ, (Nat.fib (3 * m) : ℤ) = (3 : ℤ) ^ (a + 1) * v ∧
      ¬(3 : ℤ) ∣ v := by
  have hm : (3 : ℤ) ∣ (Nat.fib m : ℤ) := by
    refine ⟨(3 : ℤ) ^ (a - 1) * u, ?_⟩
    calc
      (Nat.fib m : ℤ) = (3 : ℤ) ^ a * u := hfac
      _ = (3 : ℤ) ^ ((a - 1) + 1) * u :=
        congrArg (fun k : ℕ => (3 : ℤ) ^ k * u) (by omega)
      _ = 3 * ((3 : ℤ) ^ (a - 1) * u) := by
        rw [pow_succ]
        ring
  obtain ⟨w, hw, hwunit⟩ := fib_three_mul_factor_unit m hm
  refine ⟨u * w, ?_, ?_⟩
  · rw [hw, hfac, pow_succ]
    ring
  · intro hd
    rcases (show Prime (3 : ℤ) by norm_num).dvd_mul.mp hd with hu | hw'
    · exact hunit hu
    · exact hwunit hw'

/-- `9 ∣ Fₙ` if and only if `12 ∣ n`. -/
theorem nine_dvd_fib_iff (n : ℕ) : 9 ∣ Nat.fib n ↔ 12 ∣ n := by
  have hfinite : ∀ r : Fin 24,
      Nat.fib r.val % 9 = 0 ↔ r.val % 12 = 0 := by decide
  have hr := hfinite ⟨n % 24, Nat.mod_lt n (by decide)⟩
  change Nat.fib (n % 24) % 9 = 0 ↔ (n % 24) % 12 = 0 at hr
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    fib_mod_reduce_index 9 24 fib_state_returns_nine n]
  simpa only [Nat.mod_mod_of_dvd n (by decide : 12 ∣ 24)] using hr

/-- If `4 ∣ m` and `3 ∤ m`, then `Fₘ = 3u` with `3 ∤ u`. -/
theorem fib_three_base_unit (m : ℕ) (h4 : 4 ∣ m) (h3 : ¬3 ∣ m) :
    ∃ u : ℤ, (Nat.fib m : ℤ) = 3 * u ∧ ¬(3 : ℤ) ∣ u := by
  have hdiv : 3 ∣ Nat.fib m := (three_dvd_fib_iff m).2 h4
  obtain ⟨u, hu⟩ := hdiv
  refine ⟨u, by exact_mod_cast hu, ?_⟩
  intro hu3
  have hu3Nat : 3 ∣ u := by exact_mod_cast hu3
  have h9 : 9 ∣ Nat.fib m := by
    obtain ⟨v, rfl⟩ := hu3Nat
    rw [hu]
    exact ⟨v, by ring⟩
  have h12 : 12 ∣ m := (nine_dvd_fib_iff m).1 h9
  exact h3 ((show 3 ∣ 12 by norm_num).trans h12)

/-- If `4 ∣ m` and `3 ∤ m`, then `F_{3^a m} = 3^{a+1} u` with `3 ∤ u`. -/
theorem fib_three_pow_mul_unit (a m : ℕ) (h4 : 4 ∣ m) (h3 : ¬3 ∣ m) :
    ∃ u : ℤ, (Nat.fib (3 ^ a * m) : ℤ) = (3 : ℤ) ^ (a + 1) * u ∧
      ¬(3 : ℤ) ∣ u := by
  induction a with
  | zero =>
      obtain ⟨u, hu, hunit⟩ := fib_three_base_unit m h4 h3
      exact ⟨u, by simpa using hu, hunit⟩
  | succ a ih =>
      obtain ⟨u, hu, hunit⟩ := ih
      obtain ⟨v, hv, hvunit⟩ :=
        fib_three_mul_lift_unit (3 ^ a * m) (a + 1) u hu (by omega) hunit
      refine ⟨v, ?_, hvunit⟩
      have hi : 3 ^ a.succ * m = 3 * (3 ^ a * m) := by
        rw [pow_succ]
        ring
      rw [hi, hv]

end FibonacciCriterion
