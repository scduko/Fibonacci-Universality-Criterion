import FibonacciCriterion.Escalation.BinaryOneTwoRank

/-!
# Escalation of `⟨1,2⟩`

Let `v` and `u` be orthogonal vectors of norms 1 and 2 in a form that
represents 5. The remainder `r` of a vector of norm 5 after projection onto
`v` and reduction along `u` is orthogonal to `v`, with `β(r, u) ∈ {0, 1}` and
`1 ≤ P(r) ≤ 5`; if `β(r, u) = 1`, then `P(r) ∈ {1, 4, 5}`
(`exists_oneTwo_reduced_vector`). This is the second case of the proof of
Proposition 3.1. The manuscript excludes pairing 1 with third norm 2 or 3 by
listing the small values of the binary part; here the equation
`5 = a² + 2k² + 2k + P(r)` is reduced modulo 4 (`oneTwo_third_norm_of_pairing_one`).
No classification up to isometry is stated.
-/

namespace FibonacciCriterion
namespace Form

variable {ι : Type*} [Fintype ι]

/-- If `1 ≤ d ≤ 5` and `5 = a² + 2k² + 2k + d`, then `d` is 1, 4, or 5, since
`2k² + 2k ≡ 0 (mod 4)`. -/
theorem oneTwo_third_norm_of_pairing_one (a k d : ℤ)
    (hd : 1 ≤ d) (hd' : d ≤ 5)
    (he : 5 = a ^ 2 + 2 * k ^ 2 + 2 * k + d) :
    d = 1 ∨ d = 4 ∨ d = 5 := by
  have ha : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have hk : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  have hm := congrArg (fun t : ℤ => t % 4) he
  rcases ha with ha | ha | ha | ha <;>
    rcases hk with hk | hk | hk | hk <;>
    norm_num [pow_two, Int.add_emod, Int.mul_emod, ha, hk] at hm <;> omega

/-- If `v` and `u` are orthogonal vectors of norms 1 and 2 and the form
represents 5, some vector `r` orthogonal to `v` has `β(r, u) ∈ {0, 1}` and
`1 ≤ P(r) ≤ 5`, and `P(r) ∈ {1, 4, 5}` when `β(r, u) = 1`. -/
theorem exists_oneTwo_reduced_vector (P : Form ι) (v u : ι → ℤ)
    (hv : P.eval v = 1) (hu : P.eval u = 2)
    (huv : P.pairing u v = 0) (h5 : P.Represents 5) :
    ∃ r : ι → ℤ, P.pairing r v = 0 ∧
      (P.pairing r u = 0 ∨ P.pairing r u = 1) ∧
      1 ≤ P.eval r ∧ P.eval r ≤ 5 ∧
      (P.pairing r u = 1 →
        P.eval r = 1 ∨ P.eval r = 4 ∨ P.eval r = 5) := by
  obtain ⟨x, hx⟩ := h5
  have hx' : P.eval x = 5 := by simpa using hx
  let y := P.unitRemainder v x
  let r := P.normTwoRemainder u y
  have hrv : P.pairing r v = 0 :=
    P.normTwoRemainder_orthogonal u y v (P.unitRemainder_orthogonal v x hv) huv
  have he : P.pairing r u = 0 ∨ P.pairing r u = 1 :=
    P.pairing_normTwoRemainder_cases u y hu
  have hd : 1 ≤ P.eval r := by
    have hp := P.eval_pos r (P.oneTwoRemainder_ne_zero v u x hv hu hx')
    omega
  have hunit : 5 = (P.pairing x v) ^ 2 + P.eval y := by
    simpa only [hx'] using P.eval_unit_decomposition v x hv
  have hd' : P.eval r ≤ 5 := by
    have hr := P.eval_normTwoRemainder_le u y hu
    nlinarith [sq_nonneg (P.pairing x v)]
  refine ⟨r, hrv, he, hd, hd', ?_⟩
  intro hone
  have hrem : P.pairing y u % 2 = 1 := by
    rw [← P.pairing_normTwoRemainder u y hu]
    exact hone
  have hnorm := P.eval_normTwo_decomposition u y hu
  rw [hrem] at hnorm
  apply oneTwo_third_norm_of_pairing_one (P.pairing x v) (P.pairing y u / 2)
    (P.eval r) hd hd'
  dsimp only [r] at *
  nlinarith

end Form
end FibonacciCriterion
