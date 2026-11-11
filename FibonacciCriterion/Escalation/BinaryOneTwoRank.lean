import FibonacciCriterion.Escalation.NormTwoReduction
import FibonacciCriterion.ClassicalInputs.ThreeSquares.Obstruction

/-!
# The truant 5 of `⟨1,2⟩` raises the rank

For vectors `v` and `u` of norms 1 and 2, the remainder of a vector of norm 5
after projection onto `v` and reduction along `u` is nonzero
(`oneTwoRemainder_ne_zero`): otherwise `5 = a² + 2b²`, which is impossible
modulo 8 (`sq_add_two_sq_ne_five`). The manuscript shows by descent that
`⟨1,2⟩ ⊗ ℚ` does not represent 5; here the integral statement suffices.
`Escalation.BinaryOneTwo` uses it in the escalation of `⟨1,2⟩`.
-/

namespace FibonacciCriterion
namespace Form

variable {ι : Type*} [Fintype ι]

/-- `⟨1,2⟩` does not represent 5: `a² + 2b² ≢ 5 (mod 8)`. -/
theorem sq_add_two_sq_ne_five (a b : ℤ) : a ^ 2 + 2 * b ^ 2 ≠ 5 := by
  intro h
  have hm := congrArg (fun t : ℤ => t % 8) h
  rcases RegularReductions.square_mod_eight a with ha | ha | ha <;>
    rcases RegularReductions.square_mod_eight b with hb | hb | hb <;>
    norm_num [Int.add_emod, Int.mul_emod, ha, hb] at hm

/-- If `v` has norm 1, `u` has norm 2, and `x` has norm 5, the remainder of `x`
after projection onto `v` and reduction along `u` is nonzero. -/
theorem oneTwoRemainder_ne_zero (P : Form ι) (v u x : ι → ℤ)
    (hv : P.eval v = 1) (hu : P.eval u = 2) (hx : P.eval x = 5) :
    P.normTwoRemainder u (P.unitRemainder v x) ≠ 0 := by
  intro hz
  have heq : P.unitRemainder v x =
      (P.pairing (P.unitRemainder v x) u / 2) • u := by
    exact sub_eq_zero.mp hz
  have he := P.eval_unit_decomposition v x hv
  rw [hx, heq, eval_smul, hu] at he
  exact sq_add_two_sq_ne_five (P.pairing x v)
    (P.pairing (P.unitRemainder v x) u / 2) (by nlinarith)

end Form
end FibonacciCriterion
