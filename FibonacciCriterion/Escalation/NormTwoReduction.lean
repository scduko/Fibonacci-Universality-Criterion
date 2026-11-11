import FibonacciCriterion.Escalation.Pairing

/-!
# Reduction along a vector of norm 2

Subtracting an integral multiple of a vector `u` of norm 2 from `x` reduces
the pairing `β(x, u)` to 0 or 1 without increasing the value of the form
(`Form.normTwoRemainder`), and preserves orthogonality to every vector
orthogonal to both `x` and `u`. This is the reduction along the vector of
norm 2 in the proof of Proposition 3.1. The ambient rank is arbitrary.
-/

namespace FibonacciCriterion
namespace Form

variable {ι : Type*} [Fintype ι]

/-- The remainder `x - ⌊β(x, u) / 2⌋ u` of `x` after reduction along a vector
`u` of norm 2. -/
def normTwoRemainder (P : Form ι) (u x : ι → ℤ) : ι → ℤ :=
  x - (P.pairing x u / 2) • u

/-- The reduced pairing is `β(x, u) mod 2`. -/
theorem pairing_normTwoRemainder (P : Form ι) (u x : ι → ℤ)
    (hu : P.eval u = 2) :
    P.pairing (P.normTwoRemainder u x) u = P.pairing x u % 2 := by
  unfold normTwoRemainder
  rw [pairing_sub_left, pairing_smul_left, pairing_self, hu]
  omega

/-- The reduced pairing is 0 or 1. -/
theorem pairing_normTwoRemainder_cases (P : Form ι) (u x : ι → ℤ)
    (hu : P.eval u = 2) :
    P.pairing (P.normTwoRemainder u x) u = 0 ∨
      P.pairing (P.normTwoRemainder u x) u = 1 := by
  rw [pairing_normTwoRemainder P u x hu]
  omega

/-- The value lost in the reduction: with `k = ⌊β(x, u) / 2⌋` and
`e = β(x, u) mod 2`, `P(x) = P(r) + 2k² + 2ke`, where `r` is the remainder. -/
theorem eval_normTwo_decomposition (P : Form ι) (u x : ι → ℤ)
    (hu : P.eval u = 2) :
    P.eval x = P.eval (P.normTwoRemainder u x) +
      2 * (P.pairing x u / 2) ^ 2 +
      2 * (P.pairing x u / 2) * (P.pairing x u % 2) := by
  have hsplit : x = (P.pairing x u / 2) • u + P.normTwoRemainder u x := by
    unfold normTwoRemainder
    abel
  calc
    P.eval x = P.eval ((P.pairing x u / 2) • u +
        P.normTwoRemainder u x) := congrArg P.eval hsplit
    _ = _ := by
      rw [eval_add_pairing, eval_smul, pairing_smul_left,
        pairing_smul_right, hu, P.pairing_comm u (P.normTwoRemainder u x),
        pairing_normTwoRemainder P u x hu]
      ring

/-- The reduction does not increase the value: `P(r) ≤ P(x)`. -/
theorem eval_normTwoRemainder_le (P : Form ι) (u x : ι → ℤ)
    (hu : P.eval u = 2) :
    P.eval (P.normTwoRemainder u x) ≤ P.eval x := by
  have he := P.eval_normTwo_decomposition u x hu
  have hrem0 : 0 ≤ P.pairing x u % 2 := by omega
  have hrem1 : P.pairing x u % 2 ≤ 1 := by omega
  by_cases hk : 0 ≤ P.pairing x u / 2
  · have hprod := mul_nonneg hk hrem0
    nlinarith [sq_nonneg (P.pairing x u / 2)]
  · have hk' : P.pairing x u / 2 ≤ -1 := by omega
    have hsum : P.pairing x u / 2 + P.pairing x u % 2 ≤ 0 := by omega
    have hprod := mul_nonneg_of_nonpos_of_nonpos (le_of_lt (lt_of_not_ge hk)) hsum
    nlinarith

/-- If `x` and `u` are orthogonal to `v`, so is the remainder of `x`. In
particular, the reduction keeps orthogonality to the vector of norm 1. -/
theorem normTwoRemainder_orthogonal (P : Form ι) (u x v : ι → ℤ)
    (hxv : P.pairing x v = 0) (huv : P.pairing u v = 0) :
    P.pairing (P.normTwoRemainder u x) v = 0 := by
  unfold normTwoRemainder
  rw [pairing_sub_left, pairing_smul_left, hxv, huv]
  ring

end Form
end FibonacciCriterion
