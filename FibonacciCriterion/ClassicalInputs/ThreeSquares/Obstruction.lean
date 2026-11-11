import FibonacciCriterion.ClassicalInputs.ThreeSquares.Scaling

/-!
# The three-square obstruction

No integer `≡ 7 (mod 8)` is a sum of three squares. With the descent by 4 of
`ClassicalInputs.ThreeSquares.Scaling`, no integer `4^a (8b + 7)` is one
(`not_threeSquares_four_pow`). The file also records the squares modulo 8 and
9. The converse is the three-square theorem, in
`ClassicalInputs.ThreeSquares.Theorem`.
-/

namespace FibonacciCriterion.RegularReductions

/-- Every square is 0, 1, or 4 modulo 8. -/
theorem square_mod_eight (x : ℤ) :
    x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have hx : 0 ≤ x % 8 ∧ x % 8 < 8 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  obtain ⟨hx0, hx1⟩ := hx
  interval_cases hxr : x % 8 <;>
    norm_num [pow_two, Int.mul_emod, hxr]

/-- Every square is 0, 1, 4, or 7 modulo 9. -/
theorem square_mod_nine (x : ℤ) :
    x ^ 2 % 9 = 0 ∨ x ^ 2 % 9 = 1 ∨
      x ^ 2 % 9 = 4 ∨ x ^ 2 % 9 = 7 := by
  have hx0 : 0 ≤ x % 9 := Int.emod_nonneg _ (by norm_num)
  have hx9 : x % 9 < 9 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases hx : x % 9 <;>
    norm_num [pow_two, Int.mul_emod, hx]

/-- No integer `≡ 7 (mod 8)` is a sum of three squares. -/
theorem not_threeSquares_mod_eight (n : ℤ) (hn : n % 8 = 7) :
    ¬ ThreeSquares n := by
  rintro ⟨x, y, z, h⟩
  have hm := congrArg (fun t : ℤ => t % 8) h
  rcases square_mod_eight x with hx | hx | hx <;>
    rcases square_mod_eight y with hy | hy | hy <;>
    rcases square_mod_eight z with hz | hz | hz <;>
    norm_num [Int.add_emod, hx, hy, hz, hn] at hm

/-- No integer `4^a (8b + 7)` is a sum of three squares. -/
theorem not_threeSquares_four_pow (a : ℕ) (b : ℤ) :
    ¬ ThreeSquares (4 ^ a * (8 * b + 7)) := by
  rw [threeSquares_four_pow_mul_iff]
  apply not_threeSquares_mod_eight
  omega

end FibonacciCriterion.RegularReductions
