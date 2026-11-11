import Mathlib

/-!
# A quadratic congruence over `𝔽_p` (Lemma 5.9)

For a prime `p ≥ 5` and units `u₀, q₀` modulo `p`, some `t` with
`|t| ≤ (p - 1) / 2` makes `u₀ - q₀ t²` a nonzero square modulo `p`; if `u₀` is
a nonsquare, then `t ≠ 0` (`exists_sub_mul_sq_square`).

As in the manuscript, the proof counts points with the quadratic character
`χ`: `y² = t² - ξ` has `p - 1` solutions, so `Σ_t χ(t² - ξ) = -1`
(`sum_quadraticChar_sq_sub`), and the conic `x² + q₀ t² = u₀` has
`p - χ(-q₀) ≥ p - 1` points, at most two of them with `x = 0`
(`exists_conic_point`).
-/

namespace FibonacciCriterion

open Finset

namespace QuadraticCongruence

variable {p : ℕ} [hp : Fact p.Prime]

theorem ringChar_zmod_ne_two (h5 : 5 ≤ p) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

/-- The number of solutions of `y² = a` is `χ(a) + 1`. -/
theorem card_sqrts (h5 : 5 ≤ p) (a : ZMod p) :
    ((univ.filter fun y : ZMod p => y ^ 2 = a).card : ℤ) = quadraticChar (ZMod p) a + 1 := by
  have := quadraticChar_card_sqrts (ringChar_zmod_ne_two h5) a
  simpa [Set.toFinset_ofPred] using this

/-- The size of a set of pairs is the sum of the sizes of its fibres over the
first coordinate. -/
theorem card_pairs (P : ZMod p → ZMod p → Prop) [∀ t y, Decidable (P t y)] :
    (univ.filter fun ty : ZMod p × ZMod p => P ty.1 ty.2).card =
      ∑ t : ZMod p, (univ.filter fun y : ZMod p => P t y).card := by
  rw [card_filter, Fintype.sum_prod_type]
  simp only [card_filter]

/-- For `ξ ≠ 0`, `Σ_t χ(t² - ξ) = -1`: the equation `y² = t² - ξ`, that is
`(t - y)(t + y) = ξ`, has `p - 1` solutions. -/
theorem sum_quadraticChar_sq_sub (h5 : 5 ≤ p) (ξ : ZMod p) (hξ : ξ ≠ 0) :
    ∑ t : ZMod p, quadraticChar (ZMod p) (t ^ 2 - ξ) = -1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  -- `#{(t, y) : y² = t² - ξ} = #{(a, b) : a b = ξ} = p - 1`.
  have hpairs : (univ.filter fun ty : ZMod p × ZMod p => ty.2 ^ 2 = ty.1 ^ 2 - ξ).card =
      (univ.filter fun ab : ZMod p × ZMod p => ab.1 * ab.2 = ξ).card := by
    apply card_nbij' (fun ty => (ty.1 - ty.2, ty.1 + ty.2))
      (fun ab => ((ab.1 + ab.2) / 2, (ab.2 - ab.1) / 2))
    · intro ty hty
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hty ⊢
      linear_combination -hty
    · intro ab hab
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hab ⊢
      field_simp
      linear_combination -4 * hab
    · intro ty _
      ext <;> simp <;> field_simp <;> ring
    · intro ab _
      ext <;> simp <;> field_simp <;> ring
  have hprod : (univ.filter fun ab : ZMod p × ZMod p => ab.1 * ab.2 = ξ).card = p - 1 := by
    rw [card_pairs (fun a b => a * b = ξ)]
    have hfib : ∀ a : ZMod p, (univ.filter fun b : ZMod p => a * b = ξ).card =
        if a = 0 then 0 else 1 := by
      intro a
      split_ifs with ha
      · subst ha
        simp [eq_comm, hξ]
      · rw [card_eq_one]
        refine ⟨ξ / a, ?_⟩
        ext b
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro h
          field_simp
          linear_combination h
        · rintro rfl
          field_simp
    simp only [hfib, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add]
    rw [filter_ne' univ (0 : ZMod p), card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have hcount : ∑ t : ZMod p, ((univ.filter fun y : ZMod p => y ^ 2 = t ^ 2 - ξ).card : ℤ) =
      (p : ℤ) - 1 := by
    have h := card_pairs (fun t y : ZMod p => y ^ 2 = t ^ 2 - ξ)
    rw [hpairs, hprod] at h
    have hp1 : 1 ≤ p := hp.out.one_lt.le
    have h' : ((p - 1 : ℕ) : ℤ) =
        ∑ t : ZMod p, ((univ.filter fun y : ZMod p => y ^ 2 = t ^ 2 - ξ).card : ℤ) := by
      exact_mod_cast h
    rw [Nat.cast_sub hp1, Nat.cast_one] at h'
    linarith
  have hsum : ∑ t : ZMod p, (quadraticChar (ZMod p) (t ^ 2 - ξ) + 1) = (p : ℤ) - 1 := by
    rw [← hcount]
    exact Finset.sum_congr rfl (fun t _ => (card_sqrts h5 (t ^ 2 - ξ)).symm)
  rw [sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one] at hsum
  linarith

/-- Lemma 5.9 over the field: the conic `x² + q₀ t² = u₀` has
`p - χ(-q₀) ≥ p - 1` points, at most two of them with `x = 0`, so some point
has `x ≠ 0`. -/
theorem exists_conic_point (h5 : 5 ≤ p) (u₀ q₀ : ZMod p) (hu : u₀ ≠ 0) (hq : q₀ ≠ 0) :
    ∃ x t : ZMod p, x ≠ 0 ∧ x ^ 2 + q₀ * t ^ 2 = u₀ := by
  set ξ := u₀ / q₀
  have hξ : ξ ≠ 0 := div_ne_zero hu hq
  set S := univ.filter fun tx : ZMod p × ZMod p => tx.2 ^ 2 = u₀ - q₀ * tx.1 ^ 2
  -- `#S = Σ_t (χ(u₀ - q₀ t²) + 1) = p - χ(-q₀)`.
  have hS : (S.card : ℤ) = p - quadraticChar (ZMod p) (-q₀) := by
    have h := card_pairs (fun t x : ZMod p => x ^ 2 = u₀ - q₀ * t ^ 2)
    have h' : (S.card : ℤ) = ∑ t : ZMod p,
        ((univ.filter fun x : ZMod p => x ^ 2 = u₀ - q₀ * t ^ 2).card : ℤ) := by
      exact_mod_cast h
    rw [h', Finset.sum_congr rfl (fun t _ => card_sqrts h5 (u₀ - q₀ * t ^ 2))]
    have hfac : ∀ t : ZMod p, quadraticChar (ZMod p) (u₀ - q₀ * t ^ 2) =
        quadraticChar (ZMod p) (-q₀) * quadraticChar (ZMod p) (t ^ 2 - ξ) := by
      intro t
      rw [← map_mul]
      congr 1
      simp only [ξ]
      field_simp
      ring
    simp only [hfac, sum_add_distrib, ← mul_sum, sum_quadraticChar_sq_sub h5 ξ hξ, sum_const,
      card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    ring
  have hχ : quadraticChar (ZMod p) (-q₀) ≤ 1 := by
    rcases quadraticChar_dichotomy (neg_ne_zero.2 hq) with h | h <;> simp [h]
  by_contra hno
  push Not at hno
  -- Every point has `x = 0`, so `S` embeds in the at most two roots of `t² = ξ`.
  have hsub : S ⊆ (univ.filter fun t : ZMod p => t ^ 2 = ξ).image fun t => (t, 0) := by
    intro tx htx
    simp only [S, mem_filter, mem_univ, true_and] at htx
    have hx : tx.2 = 0 := by
      by_contra hx
      exact hno tx.2 tx.1 hx (by linear_combination htx)
    simp only [mem_image, mem_filter, mem_univ, true_and]
    refine ⟨tx.1, ?_, by ext <;> simp [hx]⟩
    rw [hx] at htx
    simp only [ξ]
    field_simp
    linear_combination htx
  have hle := (card_le_card hsub).trans card_image_le
  have h2 : ((univ.filter fun t : ZMod p => t ^ 2 = ξ).card : ℤ) ≤ 2 := by
    rw [card_sqrts h5]
    rcases quadraticChar_dichotomy hξ with h | h <;> rw [h] <;> norm_num
  have : (S.card : ℤ) ≤ 2 := le_trans (by exact_mod_cast hle) h2
  have hp5 : (5 : ℤ) ≤ p := by exact_mod_cast h5
  linarith

end QuadraticCongruence

open QuadraticCongruence

/-- Lemma 5.9: for a prime `p ≥ 5` and integers `u₀, q₀` prime to `p`, some
integer `t` with `|t| ≤ (p - 1) / 2` makes `u₀ - q₀ t²` a nonzero square
modulo `p`. If `u₀` is a nonsquare modulo `p`, then `t ≠ 0`. -/
theorem exists_sub_mul_sq_square (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p)
    (u₀ q₀ : ℤ) (hu : (u₀ : ZMod p) ≠ 0) (hq : (q₀ : ZMod p) ≠ 0) :
    ∃ t : ℤ, t.natAbs ≤ (p - 1) / 2 ∧
      (∃ x : ZMod p, x ≠ 0 ∧ x ^ 2 = ((u₀ - q₀ * t ^ 2 : ℤ) : ZMod p)) ∧
      ((∀ y : ZMod p, y ^ 2 ≠ (u₀ : ZMod p)) → t ≠ 0) := by
  obtain ⟨x, t, hx, hxt⟩ := exists_conic_point h5 (u₀ : ZMod p) q₀ hu hq
  have hodd : p / 2 = (p - 1) / 2 := by
    have := (Fact.out : p.Prime).eq_one_or_self_of_dvd 2
    omega
  refine ⟨t.valMinAbs, hodd ▸ t.natAbs_valMinAbs_le, ⟨x, hx, ?_⟩, ?_⟩
  · push_cast
    linear_combination hxt
  · intro hns h0
    apply hns x
    have : t = 0 := by
      rw [← ZMod.coe_valMinAbs t, h0]
      simp
    rw [this] at hxt
    linear_combination hxt

end FibonacciCriterion
