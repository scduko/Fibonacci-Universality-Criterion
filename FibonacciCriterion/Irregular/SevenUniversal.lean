import FibonacciCriterion.Irregular.Subtraction

/-!
# The universal form `f ⊥ ⟨7⟩` (Proposition 6.2)

`representsFPlus_seven` is Proposition 6.2: the form `f(x, y, z) + 7w²`
represents every nonnegative integer. As in the manuscript, the proof is by
strong induction: for `49 ∣ N` it scales a representation of `N / 49` by 7;
otherwise it subtracts `7w²` so that the difference is eligible and not 7 or
10 modulo 12. For `7 ∤ N`, `w ∈ {0, 1}`. For `N = 7u`, `w` comes from the
manuscript's table, checked on every class modulo 84
(`sevenUniversalW_checked`); the two values `u = 1, 26` have explicit vectors.
The proof uses only the sufficiency direction of Proposition 3.3 and
Lemma 3.4.
-/

namespace FibonacciCriterion.Irregular

open Eligibility

/-- The choice of `w` for `N = 7u` in Proposition 6.2, read from `u mod 7` and
`u mod 12`. -/
def sevenUniversalW (u : ℕ) : ℕ :=
  match u % 7, u % 12 with
  | 1, 1 => 2
  | 1, 10 => 2
  | 2, 1 => 1
  | 2, 10 => 1
  | 3, 2 => 3
  | 3, 11 => 3
  | 3, _ => 1
  | 4, 1 => 3
  | 4, 10 => 4
  | 5, 2 => 6
  | 5, 11 => 2
  | 5, _ => 1
  | 6, 2 => 3
  | 6, 5 => 3
  | 6, _ => 2
  | _, _ => 0

/-- `sevenUniversalW u` depends only on `u` modulo 84. -/
theorem sevenUniversalW_mod (u : ℕ) : sevenUniversalW (u % 84) = sevenUniversalW u := by
  have h7 : u % 84 % 7 = u % 7 := Nat.mod_mod_of_dvd u (by norm_num)
  have h12 : u % 84 % 12 = u % 12 := Nat.mod_mod_of_dvd u (by norm_num)
  simp only [sevenUniversalW, h7, h12]

set_option maxRecDepth 100000 in
/-- The table in the proof of Proposition 6.2, checked on every class modulo 84. -/
theorem sevenUniversalW_checked :
    ∀ r : Fin 84, r.val % 7 ≠ 0 →
      sevenUniversalW r.val ≤ 6 ∧
      (((r.val : ℤ) - (sevenUniversalW r.val : ℤ) ^ 2) % 7 = 1 ∨
        ((r.val : ℤ) - (sevenUniversalW r.val : ℤ) ^ 2) % 7 = 2 ∨
        ((r.val : ℤ) - (sevenUniversalW r.val : ℤ) ^ 2) % 7 = 4) ∧
      ((r.val : ℤ) - (sevenUniversalW r.val : ℤ) ^ 2) % 12 ≠ 1 ∧
      ((r.val : ℤ) - (sevenUniversalW r.val : ℤ) ^ 2) % 12 ≠ 10 ∧
      (r.val = 1 ∨ r.val = 26 ∨ sevenUniversalW r.val ^ 2 < r.val) := by
  decide +kernel

/-- Proposition 6.2 for `7 ∤ N`: subtract `7w²` with `w ∈ {0, 1}`. -/
theorem representsFPlus_seven_of_unit
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    (N : ℤ) (hN : 0 < N) (h7 : N % 7 ≠ 0) : RepresentsFPlus 7 N := by
  by_cases hc : N % 12 = 7 ∨ N % 12 = 10
  · have hRpos : 0 < N - 7 := by omega
    have hRe : EligibleResidue (N - 7) := Or.inl (by omega)
    obtain ⟨x, y, z, hxyz⟩ := representsF_of_eligibleResidue hclass _ hRpos hRe
      (by omega) (by omega)
    exact ⟨x, y, z, 1, by rw [hxyz]; ring⟩
  · have hRe : EligibleResidue N := Or.inl h7
    obtain ⟨x, y, z, hxyz⟩ := representsF_of_eligibleResidue hclass N hN hRe
      (by omega) (by omega)
    exact ⟨x, y, z, 0, by rw [hxyz]; ring⟩

/-- If `D > 0` is a nonzero square modulo 7 and is not 1 or 10 modulo 12, then
`f` represents `7D`: the difference `7D` of Proposition 6.2 is eligible and is
not 7 or 10 modulo 12. -/
theorem representsF_seven_mul
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    (D : ℤ) (hD : 0 < D) (h7 : D % 7 = 1 ∨ D % 7 = 2 ∨ D % 7 = 4)
    (h1 : D % 12 ≠ 1) (h10 : D % 12 ≠ 10) : RepresentsF (7 * D) := by
  apply representsF_of_eligibleResidue hclass (7 * D) (by omega)
  · unfold EligibleResidue
    omega
  · omega
  · omega

/-- Proposition 6.2 for `N = 7u` with `7 ∤ u`. -/
theorem representsFPlus_seven_of_seven_mul
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    (u : ℕ) (hu7 : u % 7 ≠ 0) : RepresentsFPlus 7 ((7 * u : ℕ) : ℤ) := by
  by_cases hspecial : u = 1 ∨ u = 26
  · rcases hspecial with rfl | rfl
    · exact ⟨0, 0, 0, 1, by norm_num [f]⟩
    · exact ⟨7, 3, -6, 1, by norm_num [f]⟩
  let r : Fin 84 := ⟨u % 84, Nat.mod_lt u (by norm_num)⟩
  have hr7 : r.val % 7 ≠ 0 := by
    change u % 84 % 7 ≠ 0
    omega
  obtain ⟨hw6, hres7, hres1, hres10, hsmall⟩ := sevenUniversalW_checked r hr7
  have hw : sevenUniversalW r.val = sevenUniversalW u := sevenUniversalW_mod u
  rw [hw] at hw6 hres7 hres1 hres10 hsmall
  have hrval : ((r.val : ℕ) : ℤ) = (u : ℤ) % 84 := by
    change ((u % 84 : ℕ) : ℤ) = (u : ℤ) % 84
    push_cast
    rfl
  rw [hrval] at hres7 hres1 hres10
  have hwu : sevenUniversalW u ^ 2 < u := by
    by_cases hu84 : u < 84
    · have hru : r.val = u := Nat.mod_eq_of_lt hu84
      rw [hru] at hsmall
      omega
    · have : sevenUniversalW u ^ 2 ≤ 36 := by
        calc sevenUniversalW u ^ 2 ≤ 6 ^ 2 := Nat.pow_le_pow_left hw6 2
          _ = 36 := by norm_num
      omega
  have hwz : ((sevenUniversalW u : ℕ) : ℤ) ^ 2 < (u : ℤ) := by exact_mod_cast hwu
  generalize ((sevenUniversalW u : ℕ) : ℤ) = w at hres7 hres1 hres10 hwz
  generalize hW : w ^ 2 = W at hres7 hres1 hres10 hwz
  generalize hU : (u : ℤ) = U at hres7 hres1 hres10 hwz
  have hD7 : (U - W) % 7 = 1 ∨ (U - W) % 7 = 2 ∨ (U - W) % 7 = 4 := by omega
  obtain ⟨x, y, z, hxyz⟩ := representsF_seven_mul hclass (U - W) (by omega) hD7
    (by omega) (by omega)
  refine ⟨x, y, z, w, ?_⟩
  rw [hxyz, ← hW, ← hU]
  push_cast
  ring

/-- Proposition 6.2: `f + 7w²` represents every nonnegative integer. -/
theorem representsFPlus_seven
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    (N : ℕ) : RepresentsFPlus 7 (N : ℤ) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · exact ⟨0, 0, 0, 0, by simp [f]⟩
    by_cases h49 : 49 ∣ N
    · obtain ⟨M, rfl⟩ := h49
      obtain ⟨x, y, z, w, h⟩ := ih M (by omega)
      refine ⟨7 * x, 7 * y, 7 * z, 7 * w, ?_⟩
      rw [f_scale]
      push_cast
      rw [← h]
      ring
    by_cases h7 : 7 ∣ N
    · obtain ⟨u, rfl⟩ := h7
      exact representsFPlus_seven_of_seven_mul hclass u (by omega)
    · exact representsFPlus_seven_of_unit hclass (N : ℤ) (by exact_mod_cast hNpos)
        (by omega)

end FibonacciCriterion.Irregular
