import FibonacciCriterion.Irregular.ModTwelve
import FibonacciCriterion.Irregular.EligibilitySquareFactors
import FibonacciCriterion.Arithmetic.CenteredCRT
import FibonacciCriterion.Arithmetic.RootLifting
import FibonacciCriterion.Irregular.TransferPrimes
import FibonacciCriterion.Arithmetic.QuadraticCongruence

/-!
# Subtractions for `f ⊥ ⟨q⟩` (Lemmas 6.3, 6.4, and 6.5)

This file proves the two subtraction arguments of §6: the small subtraction
(`representsFPlus_small_subtraction`, Lemma 6.4) and the subtraction with a
square transfer (`representsFPlus_of_local_root`, Lemma 6.5). Both use the
residue class of Lemma 6.3 (`exists_seven_choice`) and the sufficiency
direction of Proposition 3.3. Lemma 6.4 then applies Lemma 3.4; Lemma 6.5
applies the square transfers of Table 3 instead.

Proposition 3.3 enters Propositions 3.5, 6.1, and 6.2 and Lemmas 6.4 and 6.5
as the hypothesis `hclass`: every `ResidualEligible` integer is represented by
`f` or by `h`. Lemmas 6.3 and 6.6 do not use it. `Criterion.Sufficiency` takes
it from the classical results, where `ClassicalInputs.Theorems` proves it
(`DeterminantSevenGenus.eligible_f_or_h`).

The file begins with the set `Q₇` of Lemma 4.4
(`irregularCoefficients`) and the facts about its elements that
`Irregular.LargeIndices` and `Irregular.EscalatorF` use.
-/

namespace FibonacciCriterion.Irregular

open Eligibility

/-- `RepresentsFPlus q n`: the form `f ⊥ ⟨q⟩`, that is `f(x, y, z) + q w²`,
represents `n`. -/
def RepresentsFPlus (q n : ℤ) : Prop :=
  ∃ x y z w : ℤ, f x y z + q * w ^ 2 = n

/-- The set `Q₇` of Lemma 4.4: the positive integers at most 21 prime to 7,
the value 7, and `7s` with `s ≤ 147` a nonsquare modulo 7. -/
def irregularCoefficients : List ℕ :=
  ((List.range 22).filter fun q => decide (0 < q ∧ q % 7 ≠ 0)) ++ [7] ++
    ((List.range 148).filter fun s => decide (s % 7 = 3 ∨ s % 7 = 5 ∨ s % 7 = 6)).map
      (fun s => 7 * s)

/-- `Q₇` has 82 elements (Lemma 4.4). -/
theorem irregularCoefficients_length : irregularCoefficients.length = 82 := by
  decide

/-- Every element of `Q₇` is positive and at most 1022; apart from 7, each is
prime to 7 or 7 times a nonsquare modulo 7. -/
theorem irregularCoefficients_checked :
    irregularCoefficients.all (fun q => decide (0 < q ∧ q ≤ 1022 ∧
      (q = 7 ∨ q % 7 ≠ 0 ∨ q % 49 = 21 ∨ q % 49 = 35 ∨ q % 49 = 42))) = true := by
  decide

/-- The facts of `irregularCoefficients_checked` for one element `q` of `Q₇`. -/
theorem irregularCoefficient_facts {q : ℕ} (hq : q ∈ irregularCoefficients) :
    0 < q ∧ q ≤ 1022 ∧ (q = 7 ∨ q % 7 ≠ 0 ∨ q % 49 = 21 ∨ q % 49 = 35 ∨ q % 49 = 42) := by
  have h := List.all_eq_true.mp irregularCoefficients_checked q hq
  simpa only [decide_eq_true_eq] using h

/-- Every `q` with `1 ≤ q ≤ 21` other than 14 is in `Q₇`. -/
theorem mem_irregularCoefficients_of_le_21 {q : ℕ} (hq : 0 < q) (hq21 : q ≤ 21)
    (hq14 : q ≠ 14) : q ∈ irregularCoefficients := by
  interval_cases q <;> first | decide | omega

/-- For `s ≤ 147` with `s ≡ 3, 5, 6 (mod 7)`, `7s` is in `Q₇`. -/
theorem mem_irregularCoefficients_of_seven_mul {s : ℕ} (hs : s ≤ 147)
    (hres : s % 7 = 3 ∨ s % 7 = 5 ∨ s % 7 = 6) : 7 * s ∈ irregularCoefficients := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨s, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, rfl⟩
  simpa only [decide_eq_true_eq] using hres

/-- A nonzero square modulo 7 is 1, 2, or 4. -/
theorem sq_zmod_seven (x : ZMod 7) (hx : x ≠ 0) : x ^ 2 = 1 ∨ x ^ 2 = 2 ∨ x ^ 2 = 4 := by
  revert x
  decide

/-- Lemma 6.3: for `q` prime to 7 or 7 times a nonsquare modulo 7
(in particular `q ∈ Q₇ \ {7}`) and any `N`, some `k` makes `N - q k²` prime to
7 or 7 times a nonzero square modulo 7 (`EligibleResidue`), and prime to 7
when `7 ∤ q`. If `7 ∤ q`, take `k = 0` when `7 ∤ N` and `k = 1` otherwise. If
`7 ∣ q` but `7 ∤ N`, take `k = 0`. Otherwise, with `q = 7s` and `N = 7u`,
Lemma 5.9 at `p = 7` supplies `k` when `7 ∤ u`, and `k = 1` gives
`u - s ≡ -s ≡ 1, 2, 4 (mod 7)` when `7 ∣ u`. Every `l ≡ k (mod 7)` has the same
property (`eligibleResidue_substitution`); this is the residue class of the
manuscript's statement. -/
theorem exists_seven_choice (N q : ℤ)
    (hq : q % 7 ≠ 0 ∨ q % 49 = 21 ∨ q % 49 = 35 ∨ q % 49 = 42) :
    ∃ k : ℤ, EligibleResidue (N - q * k ^ 2) ∧
      (q % 7 = 0 ∨ (N - q * k ^ 2) % 7 ≠ 0) := by
  by_cases hq7 : q % 7 = 0
  · obtain ⟨s, rfl⟩ : (7 : ℤ) ∣ q := Int.dvd_of_emod_eq_zero hq7
    have hs : s % 7 = 3 ∨ s % 7 = 5 ∨ s % 7 = 6 := by omega
    by_cases hN7 : N % 7 = 0
    · obtain ⟨u, rfl⟩ : (7 : ℤ) ∣ N := Int.dvd_of_emod_eq_zero hN7
      by_cases hu7 : u % 7 = 0
      · -- `7 ∣ u`: `k = 1`.
        refine ⟨1, Or.inr ?_, Or.inl hq7⟩
        omega
      · -- `7 ∤ u`: Lemma 5.9 at `p = 7`.
        have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        have hu : ((u : ℤ) : ZMod 7) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          omega
        have hs0 : ((s : ℤ) : ZMod 7) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          omega
        obtain ⟨t, -, ⟨x, hx0, hx⟩, -⟩ := exists_sub_mul_sq_square 7 (by norm_num) u s hu hs0
        refine ⟨t, Or.inr ?_, Or.inl hq7⟩
        have hw : (u - s * t ^ 2) % 7 = 1 ∨ (u - s * t ^ 2) % 7 = 2 ∨
            (u - s * t ^ 2) % 7 = 4 := by
          rcases sq_zmod_seven x hx0 with h | h | h <;> rw [h] at hx
          · have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (u - s * t ^ 2) 7).1
              (by exact_mod_cast hx)
            omega
          · have := (ZMod.intCast_eq_intCast_iff_dvd_sub 2 (u - s * t ^ 2) 7).1
              (by exact_mod_cast hx)
            omega
          · have := (ZMod.intCast_eq_intCast_iff_dvd_sub 4 (u - s * t ^ 2) 7).1
              (by exact_mod_cast hx)
            omega
        have hR : 7 * u - 7 * s * t ^ 2 = 7 * (u - s * t ^ 2) := by ring
        rw [hR]
        generalize u - s * t ^ 2 = w at hw
        omega
    · -- `7 ∤ N`: `k = 0`.
      exact ⟨0, Or.inl (by simpa using hN7), Or.inl hq7⟩
  · -- `7 ∤ q`: one of `k = 0, 1` avoids `q k² ≡ N (mod 7)`.
    by_cases hN7 : N % 7 = 0
    · refine ⟨1, Or.inl ?_, Or.inr ?_⟩ <;> omega
    · exact ⟨0, Or.inl (by simpa using hN7), Or.inr (by simpa using hN7)⟩

/-- A positive eligible integer not divisible by 49 (`EligibleResidue`) that is
not 7 or 10 modulo 12 is represented by `f`: the hypothesis `hclass` (the
sufficiency direction of Proposition 3.3) represents it by `f` or `h`, and
Lemma 3.4 gives `f`. -/
theorem representsF_of_eligibleResidue
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    (R : ℤ) (hR : 0 < R) (he : EligibleResidue R)
    (h7 : R % 12 ≠ 7) (h10 : R % 12 ≠ 10) : RepresentsF R := by
  have hRnat : ((R.toNat : ℕ) : ℤ) = R := Int.toNat_of_nonneg hR.le
  have hpos : 0 < R.toNat := by omega
  have helig : ResidualEligible R.toNat := by
    apply (eligibleResidue_iff_residualEligible R.toNat hpos).mp
    rwa [hRnat]
  have hc := hclass R.toNat helig
  rw [hRnat] at hc
  exact representsF_of_class_of_mod_twelve R hc h7 h10

/-- The residue pairs `(q mod 12, N mod 12)` in (7), for which the small
subtraction can fail. -/
def BadPair (q N : ℤ) : Prop :=
  (q % 12 = 0 ∧ (N % 12 = 7 ∨ N % 12 = 10)) ∨ (q % 12 = 3 ∧ N % 12 = 10) ∨
    (q % 12 = 9 ∧ N % 12 = 7)

/-- Lemma 6.4: let `q > 0` be prime to 7 or 7 times a nonsquare modulo 7 (in
particular `q ∈ Q₇ \ {7}`), and let `N > 441q`. Then `f ⊥ ⟨q⟩` represents `N`
unless `(q mod 12, N mod 12)` is one of the pairs (7). -/
theorem representsFPlus_small_subtraction
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    (q N : ℤ) (hqpos : 0 < q)
    (hq : q % 7 ≠ 0 ∨ q % 49 = 21 ∨ q % 49 = 35 ∨ q % 49 = 42)
    (hN : 441 * q < N) (hpair : ¬ BadPair q N) : RepresentsFPlus q N := by
  obtain ⟨t, ht, hunit⟩ := exists_seven_choice N q hq
  let s : ℤ := if N % 12 = 7 ∨ N % 12 = 10 then 1 else 0
  obtain ⟨k, hk6, hk7, hbound⟩ := exists_centered_crt 6 7 (by norm_num) (by norm_num)
    (by decide) s t
  have helig : EligibleResidue (N - q * k ^ 2) :=
    eligibleResidue_substitution N q t k hk7.symm ht hunit
  have hk : |k| ≤ 21 := by
    push_cast at hbound
    omega
  have hksq : k ^ 2 ≤ 441 := by
    have h0 : 0 ≤ |k| := abs_nonneg k
    have : k ^ 2 = |k| ^ 2 := (sq_abs k).symm
    nlinarith
  have hpos : 0 < N - q * k ^ 2 := by nlinarith
  obtain ⟨j, hj⟩ := Int.modEq_iff_dvd.mp hk6
  have hk' : k = s + 6 * (-j) := by
    push_cast at hj
    omega
  have hsq : k ^ 2 = s ^ 2 + 12 * (-(s * j) + 3 * j ^ 2) := by
    rw [hk']
    ring
  have hres : (N - q * k ^ 2) % 12 = (N - q * s ^ 2) % 12 := by
    rw [hsq]
    have : N - q * (s ^ 2 + 12 * (-(s * j) + 3 * j ^ 2)) =
        N - q * s ^ 2 + 12 * (-(q * (-(s * j) + 3 * j ^ 2))) := by ring
    rw [this, Int.add_mul_emod_self_left]
  have h7 : (N - q * k ^ 2) % 12 ≠ 7 := by
    rw [hres]
    unfold BadPair at hpair
    by_cases hc : N % 12 = 7 ∨ N % 12 = 10 <;> simp only [s, hc, ↓reduceIte] <;> omega
  have h10 : (N - q * k ^ 2) % 12 ≠ 10 := by
    rw [hres]
    unfold BadPair at hpair
    by_cases hc : N % 12 = 7 ∨ N % 12 = 10 <;> simp only [s, hc, ↓reduceIte] <;> omega
  obtain ⟨x, y, z, hxyz⟩ := representsF_of_eligibleResidue hclass _ hpos helig h7 h10
  exact ⟨x, y, z, k, by rw [hxyz]; ring⟩

/-- Lemma 6.5: let `q` be prime to 7 or 7 times a nonsquare modulo 7, let `p`
be an odd prime of Table 3 (`p ∈ transferPrimes`, `p ≠ 2`: the primes of `P₇`
and 3), and let `q k₀² ≡ N (mod p)` with `p ∤ q k₀`. If
`N > q ⌊7p²/2⌋²`, then `f ⊥ ⟨q⟩` represents `N`. -/
theorem representsFPlus_of_local_root
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    (q N p k₀ : ℕ)
    (hq : (q : ℤ) % 7 ≠ 0 ∨ (q : ℤ) % 49 = 21 ∨ (q : ℤ) % 49 = 35 ∨ (q : ℤ) % 49 = 42)
    (hp : (p : ℤ) ∈ transferPrimes) (hp2 : p ≠ 2)
    (hqp : q % p ≠ 0) (hk₀ : k₀ % p ≠ 0) (hroot : N % p = q * k₀ ^ 2 % p)
    (hN : q * (7 * p ^ 2 / 2) ^ 2 < N) : RepresentsFPlus (q : ℤ) (N : ℤ) := by
  obtain ⟨hprime, hcop⟩ := transfer_prime_facts p hp
  obtain ⟨r, _, _, hr⟩ := RootLifting.odd_prime_square_root_lift p q k₀ N hprime hp2
    hqp hk₀ hroot.symm
  obtain ⟨t, ht, hunit⟩ := exists_seven_choice (N : ℤ) (q : ℤ) hq
  have hcop2 : Nat.Coprime 7 (p ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
  obtain ⟨k, hk7, hkp, hbound⟩ := exists_centered_crt 7 (p ^ 2) (by norm_num)
    (pow_pos hprime.pos 2) hcop2 t (r : ℤ)
  have helig : EligibleResidue ((N : ℤ) - (q : ℤ) * k ^ 2) :=
    eligibleResidue_substitution (N : ℤ) (q : ℤ) t k hk7.symm ht hunit
  have hkp' : Int.ModEq ((p : ℤ) ^ 2) k (r : ℤ) := by
    simpa only [Nat.cast_pow] using hkp
  have hr' : Int.ModEq ((p : ℤ) ^ 2) ((q : ℤ) * (r : ℤ) ^ 2) (N : ℤ) := by
    simpa only [Nat.cast_pow, Nat.cast_mul] using Int.natCast_modEq_iff.mpr hr
  have hcong : Int.ModEq ((p : ℤ) ^ 2) ((q : ℤ) * k ^ 2) (N : ℤ) :=
    ((hkp'.pow 2).mul_left (q : ℤ)).trans hr'
  have hk : |k| ≤ ((7 * p ^ 2 / 2 : ℕ) : ℤ) := by
    have hdiv : ((7 * p ^ 2 / 2 : ℕ) : ℤ) = (7 * (p : ℤ) ^ 2) / 2 := by
      push_cast
      rfl
    rw [hdiv]
    push_cast at hbound
    omega
  have hksq : k ^ 2 ≤ ((7 * p ^ 2 / 2 : ℕ) : ℤ) ^ 2 := by
    have h0 : 0 ≤ |k| := abs_nonneg k
    have : k ^ 2 = |k| ^ 2 := (sq_abs k).symm
    rw [this]
    exact pow_le_pow_left₀ h0 hk 2
  have hN' : (q : ℤ) * ((7 * p ^ 2 / 2 : ℕ) : ℤ) ^ 2 < (N : ℤ) := by
    exact_mod_cast hN
  have hqz : (0 : ℤ) ≤ q := by positivity
  have hpos : 0 < (N : ℤ) - (q : ℤ) * k ^ 2 := by nlinarith
  obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp hcong
  have hzpos : 0 < z := by
    by_contra h
    have hnonpos : (p : ℤ) ^ 2 * z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_gt h)
    linarith
  have huz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzpos.le
  have hu : 0 < z.toNat := by omega
  have hres : (N : ℤ) - (q : ℤ) * k ^ 2 = (p : ℤ) ^ 2 * (z.toNat : ℤ) := by
    rw [huz]
    linarith
  have hp7 : (p : ℤ) % 7 ≠ 0 := by
    have hpn : p % 7 ≠ 0 := by
      intro hzero
      have hd : 7 ∣ p := Nat.dvd_of_mod_eq_zero hzero
      have hg := Nat.gcd_eq_right hd
      change Nat.gcd p 7 = 1 at hcop
      omega
    exact_mod_cast hpn
  have he : ResidualEligible z.toNat := by
    apply residualEligible_of_square_mul (p : ℤ) z.toNat hp7 hu
    rw [← hres]
    exact helig
  obtain ⟨x, y, w, hxyz⟩ := representsF_of_mem_transferPrimes hp (hclass z.toNat he)
  exact ⟨x, y, w, k, by rw [hxyz, ← hres]; ring⟩

end FibonacciCriterion.Irregular
