import Mathlib

/-!
# Three squares and `⟨1,1,2⟩`

This file defines `ThreeSquares` and `Represents112` and proves, as in
Proposition 3.2, that `⟨1,1,2⟩` represents `n` if and only if `2n` is a sum of
three squares (`represents112_iff_threeSquares_twice`). The proof is an
identity and a parity argument; it does not use the three-square theorem,
which `ClassicalInputs.ThreeSquares.Theorem` proves, taking the sufficiency
direction from atlas-lean. The file also records the squares modulo 16 and the
anisotropy of `x² + y²` modulo 3 and of `x² + 2y²` modulo 5, used in the
obstructions for `⟨1,2,3⟩`, `⟨1,1,3⟩`, and `⟨1,2,5⟩`, in the Mordell
construction for `⟨1,2,5⟩`, and in Lemma 5.8.
-/

namespace FibonacciCriterion.RegularReductions

/-- `n` is a sum of three integer squares. -/
def ThreeSquares (n : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n

/-- Representation of `n` by the diagonal form `⟨1,1,2⟩`. -/
def Represents112 (n : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 2 * z ^ 2 = n

/-- If `x² + y² + z²` is even, some coordinate is even and the other two have
the same parity. -/
theorem parity_of_three_squares_even (n x y z : ℤ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 2 * n) :
    (x % 2 = y % 2 ∧ z % 2 = 0) ∨
      (x % 2 = z % 2 ∧ y % 2 = 0) ∨
      (y % 2 = z % 2 ∧ x % 2 = 0) := by
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  have hz : z % 2 = 0 ∨ z % 2 = 1 := by omega
  have hmod := congrArg (fun t : ℤ => t % 2) h
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  all_goals norm_num [Int.add_emod, Int.mul_emod, pow_two, hx, hy, hz] at hmod
  all_goals norm_num [hx, hy, hz]

/-- If `a² + b² + c² = 2n` with `a ≡ b (mod 2)` and `c` even, then `⟨1,1,2⟩`
represents `n` at `((a + b)/2, (a - b)/2, c/2)`. -/
theorem represents112_of_parity (n a b c : ℤ)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 2 * n)
    (hab : a % 2 = b % 2) (hc : c % 2 = 0) :
    Represents112 n := by
  have hsum : 2 * ((a + b) / 2) = a + b := by omega
  have hdiff : 2 * ((a - b) / 2) = a - b := by omega
  have ha : a = (a + b) / 2 + (a - b) / 2 := by omega
  have hb : b = (a + b) / 2 - (a - b) / 2 := by omega
  have hc' : c = 2 * (c / 2) := by omega
  refine ⟨(a + b) / 2, (a - b) / 2, c / 2, ?_⟩
  nlinarith [congrArg (fun t : ℤ => t ^ 2) ha,
    congrArg (fun t : ℤ => t ^ 2) hb,
    congrArg (fun t : ℤ => t ^ 2) hc']

/-- For every integer `n`, `⟨1,1,2⟩` represents `n` if and only if `2n` is a
sum of three squares. -/
theorem represents112_iff_threeSquares_twice (n : ℤ) :
    Represents112 n ↔ ThreeSquares (2 * n) := by
  constructor
  · rintro ⟨x, y, z, h⟩
    refine ⟨x + y, x - y, 2 * z, ?_⟩
    nlinarith
  · rintro ⟨x, y, z, h⟩
    rcases parity_of_three_squares_even n x y z h with hxy | hxz | hyz
    · exact represents112_of_parity n x y z h hxy.1 hxy.2
    · apply represents112_of_parity n x z y _ hxz.1 hxz.2
      nlinarith
    · apply represents112_of_parity n y z x _ hyz.1 hyz.2
      nlinarith

/-- Every square is 0, 1, 4, or 9 modulo 16. -/
theorem square_mod_sixteen (x : ℤ) :
    x ^ 2 % 16 = 0 ∨ x ^ 2 % 16 = 1 ∨
      x ^ 2 % 16 = 4 ∨ x ^ 2 % 16 = 9 := by
  have hlo : 0 ≤ x % 16 := Int.emod_nonneg _ (by norm_num)
  have hhi : x % 16 < 16 := Int.emod_lt_of_pos _ (by norm_num)
  generalize hr : x % 16 = r at hlo hhi ⊢
  interval_cases r <;>
    norm_num [pow_two, Int.mul_emod, hr]

/-- If `3 ∣ x² + y²`, then 3 divides both `x` and `y`. -/
theorem dvd_three_of_sq_add_sq (x y : ℤ)
    (h : (x ^ 2 + y ^ 2) % 3 = 0) : x % 3 = 0 ∧ y % 3 = 0 := by
  have hx0 : 0 ≤ x % 3 := Int.emod_nonneg _ (by norm_num)
  have hx3 : x % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hy0 : 0 ≤ y % 3 := Int.emod_nonneg _ (by norm_num)
  have hy3 : y % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases hx : x % 3 <;> interval_cases hy : y % 3
  all_goals norm_num [pow_two, Int.add_emod, Int.mul_emod, hx, hy] at h
  all_goals norm_num [pow_two, Int.add_emod, Int.mul_emod, hx, hy]

/-- If `5 ∣ x² + 2y²`, then 5 divides both `x` and `y`. -/
theorem dvd_five_of_sq_add_two_sq (x y : ℤ)
    (h : (x ^ 2 + 2 * y ^ 2) % 5 = 0) : x % 5 = 0 ∧ y % 5 = 0 := by
  have hxlo : 0 ≤ x % 5 := Int.emod_nonneg _ (by norm_num)
  have hxhi : x % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  have hylo : 0 ≤ y % 5 := Int.emod_nonneg _ (by norm_num)
  have hyhi : y % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  generalize hxr : x % 5 = xr at hxlo hxhi h ⊢
  generalize hyr : y % 5 = yr at hylo hyhi h ⊢
  interval_cases xr <;> interval_cases yr
  all_goals
    norm_num [pow_two, Int.add_emod, Int.mul_emod, hxr, hyr] at h
  all_goals
    norm_num [hxr, hyr]

end FibonacciCriterion.RegularReductions
