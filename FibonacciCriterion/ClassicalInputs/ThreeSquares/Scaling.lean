import FibonacciCriterion.ClassicalInputs.ThreeSquares.DiagonalReductions

/-!
# Scaling and descent by 4 for three squares

A sum of three squares divisible by 4 has all coordinates even, so `4^a n`
is a sum of three squares if and only if `n` is
(`threeSquares_four_pow_mul_iff`). The two elementary steps are stated for
any diagonal form: scaling the coordinates (`diagonal_square_scale`) and
halving even coordinates (`diagonal_halve`). With the reductions of
`ClassicalInputs.ThreeSquares.DiagonalReductions`, this proves, as in
Proposition 3.2, that `⟨1,2,4⟩` and `⟨1,1,2⟩` represent the same integers
(`represents124_iff_represents112`). The three-square theorem is not used.
-/

namespace FibonacciCriterion.RegularReductions

/-- If a diagonal ternary form represents `n`, it represents `t² n`. -/
theorem diagonal_square_scale (a b c n t : ℤ)
    (h : ∃ x y z : ℤ, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = n) :
    ∃ x y z : ℤ, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = t ^ 2 * n := by
  rcases h with ⟨x, y, z, h⟩
  refine ⟨t * x, t * y, t * z, ?_⟩
  calc
    a * (t * x) ^ 2 + b * (t * y) ^ 2 + c * (t * z) ^ 2 =
        t ^ 2 * (a * x ^ 2 + b * y ^ 2 + c * z ^ 2) := by ring
    _ = t ^ 2 * n := by rw [h]

/-- If `x`, `y`, `z` are even and `a x² + b y² + c z² = 4n`, then the halved
coordinates give `n`. -/
theorem diagonal_halve {a b c n x y z : ℤ}
    (hx : x % 2 = 0) (hy : y % 2 = 0) (hz : z % 2 = 0)
    (h : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 4 * n) :
    a * (x / 2) ^ 2 + b * (y / 2) ^ 2 + c * (z / 2) ^ 2 = n := by
  obtain ⟨X, rfl⟩ : ∃ X, x = 2 * X := ⟨x / 2, by omega⟩
  obtain ⟨Y, rfl⟩ : ∃ Y, y = 2 * Y := ⟨y / 2, by omega⟩
  obtain ⟨Z, rfl⟩ : ∃ Z, z = 2 * Z := ⟨z / 2, by omega⟩
  rw [Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0),
    Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0),
    Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  linarith [show a * (2 * X) ^ 2 + b * (2 * Y) ^ 2 + c * (2 * Z) ^ 2 =
    4 * (a * X ^ 2 + b * Y ^ 2 + c * Z ^ 2) by ring]

/-- If `n` is a sum of three squares, so is `t² n`. -/
theorem threeSquares_square_scale (n t : ℤ) (h : ThreeSquares n) :
    ThreeSquares (t ^ 2 * n) := by
  simpa only [ThreeSquares, one_mul] using
    diagonal_square_scale 1 1 1 n t (by simpa only [ThreeSquares, one_mul] using h)

/-- If three squares sum to a multiple of 4, all three coordinates are even. -/
theorem threeSquares_coordinates_even (n x y z : ℤ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * n) :
    x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 := by
  have hx : 0 ≤ x % 4 ∧ x % 4 < 4 := ⟨Int.emod_nonneg _ (by norm_num),
    Int.emod_lt_of_pos _ (by norm_num)⟩
  have hy : 0 ≤ y % 4 ∧ y % 4 < 4 := ⟨Int.emod_nonneg _ (by norm_num),
    Int.emod_lt_of_pos _ (by norm_num)⟩
  have hz : 0 ≤ z % 4 ∧ z % 4 < 4 := ⟨Int.emod_nonneg _ (by norm_num),
    Int.emod_lt_of_pos _ (by norm_num)⟩
  have hm := congrArg (fun t : ℤ => t % 4) h
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hz0, hz1⟩ := hz
  interval_cases hxr : x % 4 <;> interval_cases hyr : y % 4 <;>
    interval_cases hzr : z % 4
  all_goals norm_num [Int.add_emod, Int.mul_emod, pow_two, hxr, hyr, hzr] at hm
  all_goals omega

/-- `4n` is a sum of three squares if and only if `n` is. -/
theorem threeSquares_four_mul_iff (n : ℤ) :
    ThreeSquares (4 * n) ↔ ThreeSquares n := by
  constructor
  · rintro ⟨x, y, z, h⟩
    obtain ⟨hx, hy, hz⟩ := threeSquares_coordinates_even n x y z h
    exact ⟨x / 2, y / 2, z / 2, by
      simpa only [one_mul] using diagonal_halve (a := 1) (b := 1) (c := 1) hx hy hz
        (by simpa only [one_mul] using h)⟩
  · intro h
    simpa using threeSquares_square_scale n 2 h

/-- `4^a n` is a sum of three squares if and only if `n` is. -/
theorem threeSquares_four_pow_mul_iff (n : ℤ) (a : ℕ) :
    ThreeSquares (4 ^ a * n) ↔ ThreeSquares n := by
  induction a with
  | zero => simp
  | succ a ih =>
    have he : (4 : ℤ) ^ (a + 1) * n = 4 * (4 ^ a * n) := by
      rw [pow_succ]
      ring
    rw [he, threeSquares_four_mul_iff, ih]

/-- `⟨1,1,2⟩` represents `2n` if and only if `n` is a sum of three squares. -/
theorem represents112_twice_iff_threeSquares (n : ℤ) :
    Represents112 (2 * n) ↔ ThreeSquares n := by
  rw [represents112_iff_threeSquares_twice]
  have he : 2 * (2 * n) = 4 * n := by ring
  rw [he, threeSquares_four_mul_iff]

/-- The diagonal forms `⟨1,2,4⟩` and `⟨1,1,2⟩` represent the same integers. -/
theorem represents124_iff_represents112 (n : ℤ) :
    Represents124 n ↔ Represents112 n := by
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn
  · have he : n = 2 * (n / 2) := by omega
    conv_lhs => rw [he]
    conv_rhs => rw [he]
    rw [represents124_twice_iff, represents122_iff_threeSquares,
      represents112_twice_iff_threeSquares]
  · exact represents124_iff_represents112_of_odd n hn

end FibonacciCriterion.RegularReductions
