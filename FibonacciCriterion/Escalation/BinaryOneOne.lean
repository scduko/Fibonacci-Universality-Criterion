import FibonacciCriterion.Escalation.Pairing

/-!
# Escalation of `⟨1,1⟩`

Projection onto two orthogonal vectors of norm 1 is integral. The remainder of
a vector of norm 3 is orthogonal to both and has norm 1, 2, or 3
(`exists_ternary_of_unit_pair`), so the escalations of `⟨1,1⟩` are
`⟨1,1,1⟩`, `⟨1,1,2⟩`, and `⟨1,1,3⟩`, as in the first case of the proof of
Proposition 3.1. Since its norm is at least 1, the remainder is nonzero: this
is the case `⟨1,1⟩` of Lemma 3.6, which the manuscript proves by descent. The
ambient rank is arbitrary.
-/

namespace FibonacciCriterion
namespace Form

variable {ι : Type*} [Fintype ι]

/-- If `u` and `x` are orthogonal to `v`, so is the remainder of `x` after
projection onto `u`. -/
theorem unitRemainder_preserves_orthogonal (P : Form ι)
    (v u x : ι → ℤ) (huv : P.pairing u v = 0)
    (hxv : P.pairing x v = 0) :
    P.pairing (P.unitRemainder u x) v = 0 := by
  unfold unitRemainder
  rw [pairing_sub_left, pairing_smul_left, huv, hxv]
  ring

/-- If `v` and `u` are orthogonal vectors of norm 1 and `w` has norm 3, the
remainder of `w` after projection onto `v` and then onto `u` is orthogonal to
both and has norm 1, 2, or 3. -/
theorem unitPairRemainder_of_eval_three (P : Form ι) (v u w : ι → ℤ)
    (hv : P.eval v = 1) (hu : P.eval u = 1)
    (huv : P.pairing u v = 0) (hw : P.eval w = 3) :
    let r := P.unitRemainder u (P.unitRemainder v w)
    P.pairing r v = 0 ∧ P.pairing r u = 0 ∧
      (P.eval r = 1 ∨ P.eval r = 2 ∨ P.eval r = 3) := by
  dsimp only
  refine ⟨P.unitRemainder_preserves_orthogonal v u _ huv
    (P.unitRemainder_orthogonal v w hv),
    P.unitRemainder_orthogonal u _ hu, ?_⟩
  have he₁ := P.eval_unit_decomposition v w hv
  have he₂ := P.eval_unit_decomposition u (P.unitRemainder v w) hu
  have hn := P.eval_nonneg (P.unitRemainder u (P.unitRemainder v w))
  rw [hw, he₂] at he₁
  generalize ha : P.pairing w v = a at he₁
  generalize hb : P.pairing (P.unitRemainder v w) u = b at he₁
  have ha₀ : -1 ≤ a := by nlinarith [sq_nonneg b, sq_nonneg (a + 2)]
  have ha₁ : a ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg (a - 2)]
  have hb₀ : -1 ≤ b := by nlinarith [sq_nonneg a, sq_nonneg (b + 2)]
  have hb₁ : b ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg (b - 2)]
  interval_cases a <;> interval_cases b <;> norm_num at he₁ ⊢ <;> omega

/-- If the form represents 3, then for orthogonal vectors `v` and `u` of norm 1
some vector `r` is orthogonal to both and has norm 1, 2, or 3. The three
vectors need not extend to a basis. -/
theorem exists_ternary_of_unit_pair (P : Form ι) (v u : ι → ℤ)
    (hv : P.eval v = 1) (hu : P.eval u = 1)
    (huv : P.pairing u v = 0) (h3 : P.Represents 3) :
    ∃ r : ι → ℤ, P.pairing r v = 0 ∧ P.pairing r u = 0 ∧
      (P.eval r = 1 ∨ P.eval r = 2 ∨ P.eval r = 3) := by
  obtain ⟨w, hw⟩ := h3
  have hw' : P.eval w = 3 := by simpa using hw
  exact ⟨P.unitRemainder u (P.unitRemainder v w),
    P.unitPairRemainder_of_eval_three v u w hv hu huv hw'⟩

end Form
end FibonacciCriterion
