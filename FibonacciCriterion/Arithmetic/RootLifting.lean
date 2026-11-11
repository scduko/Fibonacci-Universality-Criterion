import Mathlib

/-!
# Lifting a root of `q k² ≡ N` from `p` to `p²`

For an odd prime `p` with `p ∤ qk`, a root `k` of `q k² ≡ N (mod p)` lifts to
a root modulo `p²` with the same residue modulo `p`
(`odd_prime_square_root_lift`). Lemma 6.5 uses this lift; the manuscript
cites Hensel's lemma, and here it is one Newton step with a Bézout inverse of
the derivative `2qk`, without `p`-adic numbers.
-/

namespace FibonacciCriterion.RootLifting

/-- One Newton step: if `q k² ≡ N (mod p)` and `a` inverts `2qk` modulo `p`,
then some `r ≡ k (mod p)` satisfies `q r² ≡ N (mod p²)`. -/
theorem square_root_lift_of_inverse (p q k N a b : ℤ)
    (hroot : Int.ModEq p (q * k ^ 2) N)
    (hinverse : 1 = 2 * q * k * a + p * b) :
    ∃ r : ℤ, Int.ModEq p r k ∧ Int.ModEq (p ^ 2) (q * r ^ 2) N := by
  obtain ⟨d, hd⟩ := Int.modEq_iff_add_fac.mp hroot
  refine ⟨k + p * (a * d), ?_, ?_⟩
  · exact Int.modEq_add_fac_self
  · apply Int.modEq_iff_add_fac.mpr
    refine ⟨b * d - q * a ^ 2 * d ^ 2, ?_⟩
    linear_combination hd + (p * d) * hinverse

/-- For an odd prime `p` with `p ∤ q` and `p ∤ k`, a root `k` of
`q k² ≡ N (mod p)` lifts to a root modulo `p²` congruent to `k` modulo `p`. -/
theorem odd_prime_square_root_lift_int (p q k : ℕ) (N : ℤ)
    (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hq : q % p ≠ 0) (hk : k % p ≠ 0)
    (hroot : Int.ModEq (p : ℤ) ((q : ℤ) * (k : ℤ) ^ 2) N) :
    ∃ r : ℤ, Int.ModEq (p : ℤ) r (k : ℤ) ∧
      Int.ModEq ((p : ℤ) ^ 2) ((q : ℤ) * r ^ 2) N := by
  have hq' : ¬p ∣ q := fun h => hq (Nat.mod_eq_zero_of_dvd h)
  have hk' : ¬p ∣ k := fun h => hk (Nat.mod_eq_zero_of_dvd h)
  have htwo : ¬p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) h
    exact hodd (by have := hp.two_le; omega)
  have hderivative : Nat.Coprime (2 * q * k) p :=
    (hp.coprime_iff_not_dvd.mpr (hp.not_dvd_mul (hp.not_dvd_mul htwo hq') hk')).symm
  obtain ⟨a, ha⟩ := Int.mod_coprime hderivative
  obtain ⟨b, hb⟩ := Int.modEq_iff_add_fac.mp ha
  have hinverse : (1 : ℤ) = 2 * (q : ℤ) * (k : ℤ) * a + (p : ℤ) * b := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb
  exact square_root_lift_of_inverse (p : ℤ) (q : ℤ) (k : ℤ) N a b hroot hinverse

/-- The lift in natural numbers: the root modulo `p²` can be chosen below
`p²`, congruent to `k` modulo `p`. -/
theorem odd_prime_square_root_lift (p q k N : ℕ)
    (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hq : q % p ≠ 0) (hk : k % p ≠ 0)
    (hroot : Nat.ModEq p (q * k ^ 2) N) :
    ∃ r : ℕ, r < p ^ 2 ∧ Nat.ModEq p r k ∧ Nat.ModEq (p ^ 2) (q * r ^ 2) N := by
  have hrootZ : Int.ModEq (p : ℤ) ((q : ℤ) * (k : ℤ) ^ 2) (N : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using Int.natCast_modEq_iff.mpr hroot
  obtain ⟨R, hR, hRN⟩ := odd_prime_square_root_lift_int p q k (N : ℤ)
    hp hodd hq hk hrootZ
  have hpos : 0 < (p : ℤ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hp.pos)
  obtain ⟨r, hrlt, hr⟩ := Int.existsUnique_equiv_nat R hpos
  refine ⟨r, by exact_mod_cast hrlt, ?_, ?_⟩
  · apply Int.natCast_modEq_iff.mp
    have hdiv : (p : ℤ) ∣ (p : ℤ) ^ 2 := ⟨p, by ring⟩
    exact (hr.of_dvd hdiv).trans hR
  · apply Int.natCast_modEq_iff.mp
    have hz := ((hr.pow 2).mul_left (q : ℤ)).trans hRN
    simpa only [Nat.cast_mul, Nat.cast_pow] using hz

end FibonacciCriterion.RootLifting
