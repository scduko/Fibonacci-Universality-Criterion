import FibonacciCriterion.Forms

/-!
# The pairing and the binary escalators

The bilinear pairing `β(x, y) = xᵀ G y` of a form with Gram matrix `G`
(`Form.pairing`), its basic identities, and the orthogonal splitting along a
vector of norm 1 (`Form.unitRemainder`). A form that represents 1 and 2
contains orthogonal vectors of norms 1 and 1, or 1 and 2
(`exists_first_binary_pair`), which span `⟨1,1⟩` or `⟨1,2⟩`, the binary
escalators of §3.1. The second vector is the remainder of a vector of norm 2;
it has norm 1 or 2 (`unitRemainder_of_eval_two`), so it is nonzero, which is
the unary case of Lemma 3.6. The ambient rank is arbitrary.
-/

namespace FibonacciCriterion
namespace Form

variable {ι : Type*} [Fintype ι]

/-- The bilinear pairing `β(x, y) = xᵀ G y` of a form with Gram matrix `G`. -/
def pairing (P : Form ι) (x y : ι → ℤ) : ℤ :=
  ∑ i, ∑ j, x i * P.gram i j * y j

@[simp] theorem pairing_self (P : Form ι) (x : ι → ℤ) :
    P.pairing x x = P.eval x := rfl

/-- The pairing is symmetric, since the Gram matrix is. -/
theorem pairing_comm (P : Form ι) (x y : ι → ℤ) :
    P.pairing x y = P.pairing y x := by
  unfold pairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [P.symmetric j i]
  ring

/-- The pairing is additive in its first argument. -/
theorem pairing_add_left (P : Form ι) (x y z : ι → ℤ) :
    P.pairing (x + y) z = P.pairing x z + P.pairing y z := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

/-- The pairing respects subtraction in its first argument. -/
theorem pairing_sub_left (P : Form ι) (x y z : ι → ℤ) :
    P.pairing (x - y) z = P.pairing x z - P.pairing y z := by
  simp [pairing, sub_mul, Finset.sum_sub_distrib]

/-- The pairing is homogeneous in its first argument. -/
theorem pairing_smul_left (P : Form ι) (c : ℤ) (x y : ι → ℤ) :
    P.pairing (c • x) y = c * P.pairing x y := by
  simp [pairing, Finset.mul_sum, mul_assoc]

/-- The pairing is homogeneous in its second argument. -/
theorem pairing_smul_right (P : Form ι) (c : ℤ) (x y : ι → ℤ) :
    P.pairing x (c • y) = c * P.pairing x y := by
  rw [pairing_comm, pairing_smul_left, P.pairing_comm y x]

/-- The form is homogeneous of degree 2: `P(c x) = c² P(x)`. -/
theorem eval_smul (P : Form ι) (c : ℤ) (x : ι → ℤ) :
    P.eval (c • x) = c ^ 2 * P.eval x := by
  rw [← pairing_self, pairing_smul_left, pairing_smul_right, pairing_self]
  ring

/-- `P(x + y) = P(x) + β(x, y) + β(y, x) + P(y)`, with both mixed pairings
written out. -/
theorem eval_add_pairing (P : Form ι) (x y : ι → ℤ) :
    P.eval (x + y) = P.eval x + P.pairing x y +
      P.pairing y x + P.eval y := by
  simp only [eval, gramEval, pairing, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

/-- The pairing is additive in its second argument. -/
theorem pairing_add_right (P : Form ι) (x y z : ι → ℤ) :
    P.pairing x (y + z) = P.pairing x y + P.pairing x z := by
  rw [P.pairing_comm x (y + z), pairing_add_left,
    P.pairing_comm y x, P.pairing_comm z x]

/-- The remainder `x - β(x, v) v` of `x` after projection onto `v`. It is
integral, and orthogonal to `v` when `v` has norm 1. -/
def unitRemainder (P : Form ι) (v x : ι → ℤ) : ι → ℤ :=
  x - P.pairing x v • v

/-- If `v` has norm 1, the remainder `x - β(x, v) v` is orthogonal to `v`. -/
theorem unitRemainder_orthogonal (P : Form ι) (v x : ι → ℤ)
    (hv : P.eval v = 1) : P.pairing (P.unitRemainder v x) v = 0 := by
  unfold unitRemainder
  rw [pairing_sub_left, pairing_smul_left, pairing_self, hv]
  ring

/-- Every vector `x` is the sum of `β(x, v) v` and its remainder. -/
theorem unit_decomposition (P : Form ι) (v x : ι → ℤ) :
    x = P.pairing x v • v + P.unitRemainder v x := by
  unfold unitRemainder
  abel

/-- If `v` has norm 1, then `P(x) = β(x, v)² + P(r)`, where `r` is the
remainder of `x` after projection onto `v`. -/
theorem eval_unit_decomposition (P : Form ι) (v x : ι → ℤ)
    (hv : P.eval v = 1) :
    P.eval x = (P.pairing x v) ^ 2 + P.eval (P.unitRemainder v x) := by
  have hr := P.unitRemainder_orthogonal v x hv
  have hvr : P.pairing v (P.unitRemainder v x) = 0 := by
    rw [pairing_comm]
    exact hr
  calc
    P.eval x = P.eval (P.pairing x v • v + P.unitRemainder v x) :=
      congrArg P.eval (P.unit_decomposition v x)
    _ = (P.pairing x v) ^ 2 + P.eval (P.unitRemainder v x) := by
      rw [eval_add_pairing, eval_smul, pairing_smul_left,
        pairing_smul_right, hv, hr, hvr]
      ring

/-- If `v` has norm 1 and `w` has norm 2, the remainder of `w` after projection
onto `v` is orthogonal to `v` and has norm 1 or 2. -/
theorem unitRemainder_of_eval_two (P : Form ι) (v w : ι → ℤ)
    (hv : P.eval v = 1) (hw : P.eval w = 2) :
    P.pairing (P.unitRemainder v w) v = 0 ∧
      (P.eval (P.unitRemainder v w) = 1 ∨
        P.eval (P.unitRemainder v w) = 2) := by
  refine ⟨P.unitRemainder_orthogonal v w hv, ?_⟩
  have he := P.eval_unit_decomposition v w hv
  have hn := P.eval_nonneg (P.unitRemainder v w)
  rw [hw] at he
  generalize hc : P.pairing w v = c at he
  have hlow : -1 ≤ c := by nlinarith [sq_nonneg (c + 2)]
  have hupp : c ≤ 1 := by nlinarith [sq_nonneg (c - 2)]
  interval_cases c <;> norm_num at he ⊢ <;> omega

/-- A form that represents 1 and 2 contains orthogonal vectors `v` and `u`
with `P(v) = 1` and `P(u) ∈ {1, 2}`. The vectors need not extend to a basis
of `ℤ^ι`. -/
theorem exists_first_binary_pair (P : Form ι)
    (h1 : P.Represents 1) (h2 : P.Represents 2) :
    ∃ v u : ι → ℤ, P.eval v = 1 ∧ P.pairing u v = 0 ∧
      (P.eval u = 1 ∨ P.eval u = 2) := by
  obtain ⟨v, hv⟩ := h1
  obtain ⟨w, hw⟩ := h2
  have hv' : P.eval v = 1 := by simpa using hv
  have hw' : P.eval w = 2 := by simpa using hw
  exact ⟨v, P.unitRemainder v w, hv', P.unitRemainder_of_eval_two v w hv' hw'⟩

end Form
end FibonacciCriterion
