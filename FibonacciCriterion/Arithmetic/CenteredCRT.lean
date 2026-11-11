import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Centered Chinese remainders

Lemmas 6.4 and 6.5 combine a congruence modulo 7 with one modulo 6 or `p²`.
`exists_centered_crt` solves two congruences with coprime positive moduli
`m, n` by some `k` with `2|k| ≤ mn`; centering the residue gives the factor
1/2 in the bounds `|k| ≤ 21` and `|k| ≤ ⌊7p²/2⌋`. No primality is needed.
-/

namespace FibonacciCriterion

/-- Every residue class modulo `M > 0` has a representative `k` with
`2|k| ≤ M`. -/
theorem exists_centered_modEq (M a : ℤ) (hM : 0 < M) :
    ∃ k : ℤ, Int.ModEq M k a ∧ 2 * |k| ≤ M := by
  obtain ⟨z, hz0, hzM, hza⟩ := Int.existsUnique_equiv a hM
  by_cases hz : 2 * z ≤ M
  · refine ⟨z, hza, ?_⟩
    rwa [abs_of_nonneg hz0]
  · refine ⟨z - M, ?_, ?_⟩
    · simpa only [Int.sub_modulus_modEq_iff] using hza
    · rw [abs_of_nonpos (by omega : z - M ≤ 0)]
      omega

/-- The Chinese remainder theorem with a centered solution: for coprime
positive `m, n` and any `a, b`, some `k ≡ a (mod m)` with `k ≡ b (mod n)` has
`2|k| ≤ mn`. -/
theorem exists_centered_crt (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmn : m.Coprime n) (a b : ℤ) :
    ∃ k : ℤ, Int.ModEq (m : ℤ) k a ∧ Int.ModEq (n : ℤ) k b ∧
      2 * |k| ≤ (m : ℤ) * (n : ℤ) := by
  obtain ⟨u, hu⟩ := Int.mod_coprime hmn
  let x : ℤ := a + (m : ℤ) * (u * (b - a))
  have hxm : Int.ModEq (m : ℤ) x a := by
    dsimp [x]
    exact Int.modEq_add_fac_self
  have hxn : Int.ModEq (n : ℤ) x b := by
    have ht := (hu.mul_right (b - a)).add_left a
    have hab : a + 1 * (b - a) = b := by ring
    simpa only [x, mul_assoc, hab] using ht
  have hprod : 0 < (m : ℤ) * (n : ℤ) := by positivity
  obtain ⟨k, hk, hbound⟩ := exists_centered_modEq ((m : ℤ) * (n : ℤ)) x hprod
  exact ⟨k, (hk.of_mul_right (n : ℤ)).trans hxm,
    (hk.of_mul_left (m : ℤ)).trans hxn, hbound⟩

end FibonacciCriterion
