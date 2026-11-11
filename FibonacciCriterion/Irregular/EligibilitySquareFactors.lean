import FibonacciCriterion.Irregular.EligibilityResidues
import Mathlib.Data.Int.ModEq

/-!
# Eligibility and square factors prime to 7

Multiplying an integer by the square of an integer prime to 7 does not change
whether it is eligible: `eligible_square_checked` checks this on all classes
modulo 49, and `eligibleResidue_of_square_mul` deduces that removing such a
square preserves eligibility. Lemma 6.5 uses this to divide the difference by
`p²`. `eligibleResidue_substitution` shows that the choice in Lemma 6.3 depends
only on `k` modulo 7, as the Chinese remainder step requires.
-/

namespace FibonacciCriterion.Eligibility

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- For classes `p, u` modulo 49 with `7 ∤ p`, `p² u` is eligible if and only
if `u` is; checked over all 2,401 pairs of classes. -/
theorem eligible_square_checked :
    ∀ p u : Fin 49, (p.val : ℤ) % 7 ≠ 0 →
      (EligibleResidue ((p.val : ℤ) ^ 2 * (u.val : ℤ)) ↔
        EligibleResidue (u.val : ℤ)) := by
  decide +kernel

/-- Removing a square factor prime to 7 preserves eligibility. -/
theorem eligibleResidue_of_square_mul (p u : ℤ) (hp : p % 7 ≠ 0)
    (h : EligibleResidue (p ^ 2 * u)) : EligibleResidue u := by
  have hp0 : 0 ≤ p % 49 := Int.emod_nonneg _ (by norm_num)
  have hp49 : p % 49 < 49 := Int.emod_lt_of_pos _ (by norm_num)
  have hu0 : 0 ≤ u % 49 := Int.emod_nonneg _ (by norm_num)
  have hu49 : u % 49 < 49 := Int.emod_lt_of_pos _ (by norm_num)
  let a : Fin 49 := ⟨(p % 49).toNat, by omega⟩
  let b : Fin 49 := ⟨(u % 49).toNat, by omega⟩
  have ha : (a.val : ℤ) = p % 49 := Int.toNat_of_nonneg hp0
  have hb : (b.val : ℤ) = u % 49 := Int.toNat_of_nonneg hu0
  have ha7 : (a.val : ℤ) % 7 ≠ 0 := by
    rw [ha]
    omega
  have hab : EligibleResidue ((a.val : ℤ) ^ 2 * (b.val : ℤ)) := by
    apply eligibleResidue_of_mod_eq (b := p ^ 2 * u) _ h
    rw [ha, hb]
    simp only [pow_two, Int.mul_emod, Int.emod_emod]
  have hclass := (eligible_square_checked a b ha7).mp hab
  apply eligibleResidue_of_mod_eq (b := (b.val : ℤ)) _ hclass
  rw [hb]
  exact (Int.emod_emod u 49).symm

/-- The choice in Lemma 6.3 depends only on `k` modulo 7: if `N - q k²` is eligible,
`l ≡ k (mod 7)`, and `7 ∣ q` or `7 ∤ N - q k²`, then `N - q l²` is eligible.
If `7 ∣ q`, the difference is unchanged modulo 49; otherwise it is prime to 7
and its class modulo 7 is unchanged. -/
theorem eligibleResidue_substitution (N q k l : ℤ)
    (hkl : Int.ModEq 7 k l) (he : EligibleResidue (N - q * k ^ 2))
    (hunit : q % 7 = 0 ∨ (N - q * k ^ 2) % 7 ≠ 0) :
    EligibleResidue (N - q * l ^ 2) := by
  rcases hunit with hq | hr
  · have hqd : (7 : ℤ) ∣ q := Int.dvd_iff_emod_eq_zero.mpr hq
    obtain ⟨s, rfl⟩ := hqd
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hkl
    have hl : l = k + 7 * t := by omega
    have h49 : Int.ModEq 49 (N - 7 * s * l ^ 2) (N - 7 * s * k ^ 2) := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨s * t * (2 * k + 7 * t), ?_⟩
      rw [hl]
      ring
    exact eligibleResidue_of_mod_eq h49 he
  · apply Or.inl
    have hres : (N - q * l ^ 2) % 7 = (N - q * k ^ 2) % 7 := by
      exact (Int.ModEq.refl N).sub ((hkl.symm.pow 2).mul_left q)
    rwa [hres]

/-- For a positive integer `u`, `EligibleResidue u` agrees with
`ResidualEligible u`. `EligibleResidue` itself does not require positivity. -/
theorem eligibleResidue_iff_residualEligible (u : ℕ) (hu : 0 < u) :
    EligibleResidue (u : ℤ) ↔ Irregular.ResidualEligible u := by
  unfold EligibleResidue Irregular.ResidualEligible
  omega

/-- If `7 ∤ p`, `u > 0`, and `p² u` satisfies `EligibleResidue`, then `u`
satisfies `ResidualEligible`, the hypothesis of the sufficiency direction of
Proposition 3.3. -/
theorem residualEligible_of_square_mul (p : ℤ) (u : ℕ) (hp : p % 7 ≠ 0)
    (hu : 0 < u) (h : EligibleResidue (p ^ 2 * (u : ℤ))) :
    Irregular.ResidualEligible u := by
  exact (eligibleResidue_iff_residualEligible u hu).mp
    (eligibleResidue_of_square_mul p (u : ℤ) hp h)

end FibonacciCriterion.Eligibility
