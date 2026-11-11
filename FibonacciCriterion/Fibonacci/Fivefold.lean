import FibonacciCriterion.Fibonacci.Addition
import FibonacciCriterion.Fibonacci.SmallModuli

/-!
# Multiplying the Fibonacci index by 5

The identity `F₅ₘ = 5Fₘ · fivefoldUnit(Fₘ, Fₘ₊₁)` (`fib_five_mul_factor`)
gives the valuation formula at 5 (Lemma 2.2). The cofactor is never divisible
by 5: modulo 5 it depends only on `m` modulo the return time 20, where it is
checked (`fivefoldUnit_fib_not_dvd`). Hence `F₅ₘ` has one more factor of 5
than `Fₘ` (`fib_five_mul_lift_unit`), and `F_{5^a m}` has `a` more
(`fib_five_pow_mul_lift_unit`).
-/

namespace FibonacciCriterion

/-- The identity for `F₅ₘ` in terms of `Fₘ` and `Fₘ₊₁`, over `ℤ`. -/
theorem fib_five_mul_int (m : ℕ) :
    (Nat.fib (5 * m) : ℤ) =
      5 * (Nat.fib m : ℤ) * (Nat.fib (m + 1) : ℤ) ^ 4 -
      10 * (Nat.fib m : ℤ) ^ 2 * (Nat.fib (m + 1) : ℤ) ^ 3 +
      20 * (Nat.fib m : ℤ) ^ 3 * (Nat.fib (m + 1) : ℤ) ^ 2 -
      15 * (Nat.fib m : ℤ) ^ 4 * Nat.fib (m + 1) +
      5 * (Nat.fib m : ℤ) ^ 5 := by
  have hi2 : m + m = 2 * m := by omega
  have h2 := fib_add_int m m
  rw [hi2] at h2
  have h2s := fib_add_succ_int m m
  rw [hi2] at h2s
  have hi3 : 2 * m + m = 3 * m := by omega
  have h3 := fib_add_int (2 * m) m
  rw [hi3] at h3
  have h3s := fib_add_succ_int (2 * m) m
  rw [hi3] at h3s
  have hi4 : 3 * m + m = 4 * m := by omega
  have h4 := fib_add_int (3 * m) m
  rw [hi4] at h4
  have h4s := fib_add_succ_int (3 * m) m
  rw [hi4] at h4s
  have hi5 : 4 * m + m = 5 * m := by omega
  have h5 := fib_add_int (4 * m) m
  rw [hi5] at h5
  simp only [h5, h4, h4s, h3, h3s, h2, h2s]
  ring

/-- The cofactor `y⁴ - 2xy³ + 4x²y² - 3x³y + x⁴` of `5Fₘ` in `F₅ₘ`, where
`x = Fₘ` and `y = Fₘ₊₁`. -/
def fivefoldUnit (x y : ℤ) : ℤ :=
  y ^ 4 - 2 * x * y ^ 3 + 4 * x ^ 2 * y ^ 2 - 3 * x ^ 3 * y + x ^ 4

/-- The identity for `F₅ₘ` in factored form:
`F₅ₘ = 5Fₘ · fivefoldUnit(Fₘ, Fₘ₊₁)`. -/
theorem fib_five_mul_factor (m : ℕ) :
    (Nat.fib (5 * m) : ℤ) =
      5 * (Nat.fib m : ℤ) * fivefoldUnit (Nat.fib m) (Nat.fib (m + 1)) := by
  rw [fib_five_mul_int]
  unfold fivefoldUnit
  ring

/-- `Fₘ₊₁ ≡ F_{(m mod 20) + 1} (mod 5)`. -/
theorem fib_succ_mod_five_reduce (m : ℕ) :
    Nat.fib (m + 1) % 5 = Nat.fib (m % 20 + 1) % 5 := by
  have h := fib_mod_add_mul_period 5 20
    fib_state_returns_two_three_five_sixteen.2.2.1 (m % 20 + 1) (m / 20)
  have hi : m + 1 = m % 20 + 1 + m / 20 * 20 := by
    omega
  simpa only [hi] using h

/-- The cofactor `fivefoldUnit(Fₘ, Fₘ₊₁)` is never divisible by 5. It is
checked on the twenty classes of `m` modulo the return time 20. -/
theorem fivefoldUnit_fib_not_dvd (m : ℕ) :
    ¬(5 : ℤ) ∣ fivefoldUnit (Nat.fib m) (Nat.fib (m + 1)) := by
  rw [Int.dvd_iff_emod_eq_zero]
  have hx : (Nat.fib m : ℤ) % 5 = (Nat.fib (m % 20) : ℤ) % 5 := by
    exact_mod_cast fib_mod_reduce_index 5 20
      fib_state_returns_two_three_five_sixteen.2.2.1 m
  have hy : (Nat.fib (m + 1) : ℤ) % 5 =
      (Nat.fib (m % 20 + 1) : ℤ) % 5 := by
    exact_mod_cast fib_succ_mod_five_reduce m
  have hfinite : ∀ r : Fin 20,
      fivefoldUnit (Nat.fib r.val) (Nat.fib (r.val + 1)) % 5 ≠ 0 := by
    decide
  have hr := hfinite ⟨m % 20, Nat.mod_lt m (by decide)⟩
  change fivefoldUnit (Nat.fib (m % 20)) (Nat.fib (m % 20 + 1)) % 5 ≠ 0 at hr
  have hxq : (Nat.fib m : ℤ) ≡ (Nat.fib (m % 20) : ℤ) [ZMOD 5] := hx
  have hyq : (Nat.fib (m + 1) : ℤ) ≡
      (Nat.fib (m % 20 + 1) : ℤ) [ZMOD 5] := hy
  have htwo := ((Int.ModEq.refl 2).mul hxq).mul (hyq.pow 3)
  have hfour := ((Int.ModEq.refl 4).mul (hxq.pow 2)).mul (hyq.pow 2)
  have hthree := ((Int.ModEq.refl 3).mul (hxq.pow 3)).mul hyq
  have hpoly := ((((hyq.pow 4).sub htwo).add hfour).sub hthree).add (hxq.pow 4)
  change fivefoldUnit (Nat.fib m) (Nat.fib (m + 1)) % 5 =
      fivefoldUnit (Nat.fib (m % 20)) (Nat.fib (m % 20 + 1)) % 5 at hpoly
  intro hz
  apply hr
  rw [← hpoly]
  exact hz

/-- If `Fₘ = 5^a u` with `5 ∤ u`, then `F₅ₘ = 5^{a+1} v` with `5 ∤ v`. -/
theorem fib_five_mul_lift_unit (m a : ℕ) (u : ℤ)
    (hfac : (Nat.fib m : ℤ) = (5 : ℤ) ^ a * u)
    (hunit : ¬(5 : ℤ) ∣ u) :
    ∃ v : ℤ, (Nat.fib (5 * m) : ℤ) = (5 : ℤ) ^ (a + 1) * v ∧
      ¬(5 : ℤ) ∣ v := by
  let w := fivefoldUnit (Nat.fib m) (Nat.fib (m + 1))
  refine ⟨u * w, ?_, ?_⟩
  · calc
      (Nat.fib (5 * m) : ℤ) = 5 * (Nat.fib m : ℤ) * w :=
        fib_five_mul_factor m
      _ = 5 * ((5 : ℤ) ^ a * u) * w := by rw [hfac]
      _ = (5 : ℤ) ^ (a + 1) * (u * w) := by
        rw [pow_succ]
        ring
  · intro hd
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp hd with hu | hw
    · exact hunit hu
    · exact fivefoldUnit_fib_not_dvd m hw

/-- If `Fₘ = 5^b u` with `5 ∤ u`, then `F_{5^a m} = 5^{b+a} v` with `5 ∤ v`. -/
theorem fib_five_pow_mul_lift_unit (a m b : ℕ) (u : ℤ)
    (hfac : (Nat.fib m : ℤ) = (5 : ℤ) ^ b * u)
    (hunit : ¬(5 : ℤ) ∣ u) :
    ∃ v : ℤ, (Nat.fib (5 ^ a * m) : ℤ) = (5 : ℤ) ^ (b + a) * v ∧
      ¬(5 : ℤ) ∣ v := by
  induction a with
  | zero =>
      exact ⟨u, by simpa using hfac, hunit⟩
  | succ a ih =>
      obtain ⟨v, hv, hvunit⟩ := ih
      obtain ⟨w, hw, hwunit⟩ :=
        fib_five_mul_lift_unit (5 ^ a * m) (b + a) v hv hvunit
      refine ⟨w, ?_, hwunit⟩
      have hi : 5 ^ a.succ * m = 5 * (5 ^ a * m) := by
        rw [pow_succ]
        ring
      rw [hi, hw]
      congr 2

end FibonacciCriterion
