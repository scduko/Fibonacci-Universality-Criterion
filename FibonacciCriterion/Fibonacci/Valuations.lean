import FibonacciCriterion.Fibonacci.Fivefold
import FibonacciCriterion.Fibonacci.Threefold
import FibonacciCriterion.Fibonacci.Twofold
import FibonacciCriterion.Fibonacci.ValuationInputs
import Mathlib.Data.Nat.PadicValNat

/-!
# Fibonacci valuations at 2, 3, and 5 (Lemma 2.2)

`fibonacciValuationInputs` proves the valuation formulas of Lemma 2.2
in the form `FibonacciValuationInputs`. The manuscript cites Lengyel; here
each formula follows from base cases checked by periodicity and the
identities for `F₂ₘ`, `F₃ₘ`, and `F₅ₘ`, which raise the valuation at `p` by
1 when the index is multiplied by `p` (at 3 once `3 ∣ Fₘ`, at 2 once
`8 ∣ Fₘ`). Lucas numbers and the general lifting formula are not used.
-/

namespace FibonacciCriterion

/-- Lemma 2.2 at 5: for `n ≥ 1`, `v₅(Fₙ) = v₅(n)`, stated as `n = 5^a m` and
`Fₙ = 5^a u` with `5 ∤ m` and `5 ∤ u`. -/
theorem fibonacci_five_exact (n : ℕ) (hn : 1 ≤ n) : ∃ a m u : ℕ,
    n = 5 ^ a * m ∧ m % 5 ≠ 0 ∧
    Nat.fib n = 5 ^ a * u ∧ u % 5 ≠ 0 := by
  let a := padicValNat 5 n
  let m := n.divMaxPow 5
  let b := padicValNat 5 (Nat.fib n)
  let u := (Nat.fib n).divMaxPow 5
  have hn0 : n ≠ 0 := by omega
  have hfib0 : Nat.fib n ≠ 0 := by
    exact Nat.ne_of_gt (Nat.fib_pos.mpr hn)
  have hnprod : m * 5 ^ a = n := by
    simpa only [a, m] using Nat.divMaxPow_mul_pow_padicValNat 5 n
  have hnfac : n = 5 ^ a * m := by
    rw [← hnprod]
    exact Nat.mul_comm _ _
  have hmunit : ¬5 ∣ m := by
    simpa only [m] using Nat.not_dvd_divMaxPow (by norm_num : 1 < 5) hn0
  have hm5 : m % 5 ≠ 0 := by
    intro hm
    exact hmunit (Nat.dvd_iff_mod_eq_zero.mpr hm)
  have hfibmunitNat : ¬5 ∣ Nat.fib m := by
    intro hd
    exact hmunit ((five_dvd_fib_iff m).mp hd)
  have hfibmunit : ¬(5 : ℤ) ∣ (Nat.fib m : ℤ) := by
    exact_mod_cast hfibmunitNat
  obtain ⟨v, hv, hvunit⟩ :=
    fib_five_pow_mul_lift_unit a m 0 (Nat.fib m : ℤ)
      (by simp) hfibmunit
  have hi : 5 ^ a * m = n := hnfac.symm
  rw [hi] at hv
  have hv' : (Nat.fib n : ℤ) = (5 : ℤ) ^ a * v := by
    simpa using hv
  have hcanonNat : u * 5 ^ b = Nat.fib n := by
    simpa only [u, b] using Nat.divMaxPow_mul_pow_padicValNat 5 (Nat.fib n)
  have hcanonNat' : Nat.fib n = 5 ^ b * u := by
    rw [← hcanonNat]
    exact Nat.mul_comm _ _
  have hunitNat : ¬5 ∣ u := by
    simpa only [u] using
      Nat.not_dvd_divMaxPow (by norm_num : 1 < 5) hfib0
  have hunit : ¬(5 : ℤ) ∣ (u : ℤ) := by
    exact_mod_cast hunitNat
  have hcanon : (Nat.fib n : ℤ) = (5 : ℤ) ^ b * (u : ℤ) := by
    exact_mod_cast hcanonNat'
  have hvunitMod : v % 5 ≠ 0 := by
    intro hz
    exact hvunit (Int.dvd_iff_emod_eq_zero.mpr hz)
  have hunitMod : (u : ℤ) % 5 ≠ 0 := by
    intro hz
    exact hunit (Int.dvd_iff_emod_eq_zero.mpr hz)
  have hab : a = b :=
    pow_mul_unit_exponent_unique 5 (by norm_num) hvunitMod hunitMod
      (hv'.symm.trans hcanon)
  have hufac : Nat.fib n = 5 ^ a * u := by
    simpa only [hab] using hcanonNat'
  have hu5 : u % 5 ≠ 0 := by
    intro hu
    exact hunitNat (Nat.dvd_iff_mod_eq_zero.mpr hu)
  exact ⟨a, m, u, hnfac, hm5, hufac, hu5⟩

/-- Lemma 2.2 at 3: for `n ≥ 1`, `3 ∤ Fₙ` if `4 ∤ n`, and
`v₃(Fₙ) = 1 + v₃(n)` if `4 ∣ n`, stated as factorizations with unit parts. -/
theorem fibonacci_three_exact (n : ℕ) (hn : 1 ≤ n) :
    (¬4 ∣ n ∧ ∃ u : ℕ, Nat.fib n = u ∧ u % 3 ≠ 0) ∨
    (4 ∣ n ∧ ∃ a m u : ℕ,
      n = 3 ^ a * m ∧ m % 3 ≠ 0 ∧
      Nat.fib n = 3 ^ (a + 1) * u ∧ u % 3 ≠ 0) := by
  by_cases h4 : 4 ∣ n
  · right
    refine ⟨h4, ?_⟩
    let a := padicValNat 3 n
    let m := n.divMaxPow 3
    let b := padicValNat 3 (Nat.fib n)
    let u := (Nat.fib n).divMaxPow 3
    have hn0 : n ≠ 0 := by omega
    have hfib0 : Nat.fib n ≠ 0 := by
      exact Nat.ne_of_gt (Nat.fib_pos.mpr hn)
    have hnprod : m * 3 ^ a = n := by
      simpa only [a, m] using Nat.divMaxPow_mul_pow_padicValNat 3 n
    have hnfac : n = 3 ^ a * m := by
      rw [← hnprod]
      exact Nat.mul_comm _ _
    have hmunit : ¬3 ∣ m := by
      simpa only [m] using Nat.not_dvd_divMaxPow (by norm_num : 1 < 3) hn0
    have hm3 : m % 3 ≠ 0 := by
      intro hm
      exact hmunit (Nat.dvd_iff_mod_eq_zero.mpr hm)
    have h4m : 4 ∣ m := by
      have hcop : Nat.Coprime 4 (3 ^ a) :=
        (Nat.Coprime.pow_left a (by decide : Nat.Coprime 3 4)).symm
      apply hcop.dvd_of_dvd_mul_left
      rw [hnfac] at h4
      exact h4
    obtain ⟨v, hv, hvunit⟩ := fib_three_pow_mul_unit a m h4m hmunit
    rw [hnfac.symm] at hv
    have hcanonNat : u * 3 ^ b = Nat.fib n := by
      simpa only [u, b] using Nat.divMaxPow_mul_pow_padicValNat 3 (Nat.fib n)
    have hcanonNat' : Nat.fib n = 3 ^ b * u := by
      rw [← hcanonNat]
      exact Nat.mul_comm _ _
    have hunitNat : ¬3 ∣ u := by
      simpa only [u] using
        Nat.not_dvd_divMaxPow (by norm_num : 1 < 3) hfib0
    have hunit : ¬(3 : ℤ) ∣ (u : ℤ) := by exact_mod_cast hunitNat
    have hcanon : (Nat.fib n : ℤ) = (3 : ℤ) ^ b * (u : ℤ) := by
      exact_mod_cast hcanonNat'
    have hvunitMod : v % 3 ≠ 0 := by
      intro hz
      exact hvunit (Int.dvd_iff_emod_eq_zero.mpr hz)
    have hunitMod : (u : ℤ) % 3 ≠ 0 := by
      intro hz
      exact hunit (Int.dvd_iff_emod_eq_zero.mpr hz)
    have hab : a + 1 = b :=
      pow_mul_unit_exponent_unique 3 (by norm_num) hvunitMod hunitMod
        (hv.symm.trans hcanon)
    have hufac : Nat.fib n = 3 ^ (a + 1) * u := by
      simpa only [hab] using hcanonNat'
    have hu3 : u % 3 ≠ 0 := by
      intro hu
      exact hunitNat (Nat.dvd_iff_mod_eq_zero.mpr hu)
    exact ⟨a, m, u, hnfac, hm3, hufac, hu3⟩
  · left
    refine ⟨h4, Nat.fib n, rfl, ?_⟩
    intro hmod
    have hdiv : 3 ∣ Nat.fib n := Nat.dvd_iff_mod_eq_zero.mpr hmod
    exact h4 ((three_dvd_fib_iff n).mp hdiv)

/-- Lemma 2.2 at 2: for `n ≥ 1`, `v₂(Fₙ)` is 0 if `3 ∤ n`, 1 if
`n ≡ 3 (mod 6)`, and `v₂(n) + 2` if `6 ∣ n`, stated as factorizations with odd
parts. -/
theorem fibonacci_two_exact (n : ℕ) (hn : 1 ≤ n) :
    (¬3 ∣ n ∧ ∃ u : ℕ, Nat.fib n = u ∧ u % 2 = 1) ∨
    (n % 6 = 3 ∧ ∃ u : ℕ, Nat.fib n = 2 * u ∧ u % 2 = 1) ∨
    (6 ∣ n ∧ ∃ a m u : ℕ,
      n = 2 ^ a * m ∧ m % 2 = 1 ∧
      Nat.fib n = 2 ^ (a + 2) * u ∧ u % 2 = 1) := by
  by_cases h3 : 3 ∣ n
  · by_cases h6 : 6 ∣ n
    · right; right
      refine ⟨h6, ?_⟩
      let a := padicValNat 2 n
      let m := n.divMaxPow 2
      let b := padicValNat 2 (Nat.fib n)
      let u := (Nat.fib n).divMaxPow 2
      have hn0 : n ≠ 0 := by omega
      have hfib0 : Nat.fib n ≠ 0 := by
        exact Nat.ne_of_gt (Nat.fib_pos.mpr hn)
      have hnprod : m * 2 ^ a = n := by
        simpa only [a, m] using Nat.divMaxPow_mul_pow_padicValNat 2 n
      have hnfac : n = 2 ^ a * m := by
        rw [← hnprod]
        exact Nat.mul_comm _ _
      have hmunit : ¬2 ∣ m := by
        simpa only [m] using Nat.not_dvd_divMaxPow (by norm_num : 1 < 2) hn0
      have hm2 : m % 2 = 1 := by
        have hlt : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
        have hne : m % 2 ≠ 0 := by
          intro hz
          exact hmunit (Nat.dvd_iff_mod_eq_zero.mpr hz)
        omega
      have h2n : 2 ∣ n := (by norm_num : 2 ∣ 6).trans h6
      have ha : 1 ≤ a := by
        apply (Nat.pow_dvd_iff_le_padicValNat (by norm_num : 2 ≠ 1) hn0).mp
        simpa using h2n
      have h3m : 3 ∣ m := by
        have hcop : Nat.Coprime 3 (2 ^ a) :=
          (Nat.Coprime.pow_left a (by decide : Nat.Coprime 2 3)).symm
        apply hcop.dvd_of_dvd_mul_left
        rw [hnfac] at h3
        exact h3
      obtain ⟨v, hv, hvunit⟩ :=
        fib_two_succ_pow_mul_unit (a - 1) m h3m hm2
      have haeq : a - 1 + 1 = a := by omega
      rw [haeq, hnfac.symm, show a - 1 + 3 = a + 2 by omega] at hv
      have hcanonNat : u * 2 ^ b = Nat.fib n := by
        simpa only [u, b] using Nat.divMaxPow_mul_pow_padicValNat 2 (Nat.fib n)
      have hcanonNat' : Nat.fib n = 2 ^ b * u := by
        rw [← hcanonNat]
        exact Nat.mul_comm _ _
      have hunitNat : ¬2 ∣ u := by
        simpa only [u] using
          Nat.not_dvd_divMaxPow (by norm_num : 1 < 2) hfib0
      have hunit : ¬(2 : ℤ) ∣ (u : ℤ) := by exact_mod_cast hunitNat
      have hcanon : (Nat.fib n : ℤ) = (2 : ℤ) ^ b * (u : ℤ) := by
        exact_mod_cast hcanonNat'
      have hvunitMod : v % 2 ≠ 0 := by
        intro hz
        exact hvunit (Int.dvd_iff_emod_eq_zero.mpr hz)
      have hunitMod : (u : ℤ) % 2 ≠ 0 := by
        intro hz
        exact hunit (Int.dvd_iff_emod_eq_zero.mpr hz)
      have hab : a + 2 = b :=
        pow_mul_unit_exponent_unique 2 (by norm_num) hvunitMod hunitMod
          (hv.symm.trans hcanon)
      have hufac : Nat.fib n = 2 ^ (a + 2) * u := by
        simpa only [hab] using hcanonNat'
      have hu2 : u % 2 = 1 := by
        have hlt : u % 2 < 2 := Nat.mod_lt _ (by norm_num)
        have hne : u % 2 ≠ 0 := by
          intro hz
          exact hunitNat (Nat.dvd_iff_mod_eq_zero.mpr hz)
        omega
      exact ⟨a, m, u, hnfac, hm2, hufac, hu2⟩
    · right; left
      have hnmod : n % 6 = 3 := by
        have hmodlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
        have hmod3 : n % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h3
        have hmod6ne : n % 6 ≠ 0 := by
          intro hz
          exact h6 (Nat.dvd_iff_mod_eq_zero.mpr hz)
        omega
      refine ⟨hnmod, ?_⟩
      have h2 : 2 ∣ Nat.fib n := (two_dvd_fib_iff n).2 h3
      obtain ⟨u, hu⟩ := h2
      refine ⟨u, hu, ?_⟩
      have h4 : ¬4 ∣ Nat.fib n := by
        intro hd
        exact h6 ((four_dvd_fib_iff n).1 hd)
      have huodd : ¬2 ∣ u := by
        intro hd
        obtain ⟨v, rfl⟩ := hd
        apply h4
        refine ⟨v, ?_⟩
        rw [hu]
        ring
      have hlt : u % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hne : u % 2 ≠ 0 := by
        intro hz
        exact huodd (Nat.dvd_iff_mod_eq_zero.mpr hz)
      omega
  · left
    refine ⟨h3, Nat.fib n, rfl, ?_⟩
    have hodd : ¬2 ∣ Nat.fib n := by
      intro hd
      exact h3 ((two_dvd_fib_iff n).mp hd)
    have hlt : Nat.fib n % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hne : Nat.fib n % 2 ≠ 0 := by
      intro hz
      exact hodd (Nat.dvd_iff_mod_eq_zero.mpr hz)
    omega

/-- Lemma 2.2: the valuation formulas at 2, 3, and 5 hold. -/
theorem fibonacciValuationInputs : FibonacciValuationInputs where
  two_exact := fibonacci_two_exact
  three_exact := fibonacci_three_exact
  five_exact := fibonacci_five_exact

end FibonacciCriterion
