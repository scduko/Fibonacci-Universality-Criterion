import FibonacciCriterion.ClassicalInputs.ThreeSquares.Obstruction
import FibonacciCriterion.ClassicalInputs.Representation

/-!
# The obstruction for `⟨1,1,3⟩`

The form `x² + y² + 3z²` represents no integer `9^a (9b + 6)`
(`not_represents113_nine_pow`). As in the manuscript, the binary form
`x² + y²` is anisotropic modulo 3, so a value divisible by 9 has all
coordinates divisible by 3 and the factor 9 can be removed
(`represents113_nine_mul_iff`). The manuscript then excludes valuation 1 by
the residue of the unit part modulo 3; here the class 6 modulo 9 is
excluded by the squares modulo 9.

The converse is the statement `Regular113Sufficiency`, which
`ClassicalInputs.Regular113.Classification` proves; `criterion_of_sufficiency` combines the two
directions.
-/

namespace FibonacciCriterion.ClassicalRepresentation

namespace Regular113

/-- If `x² + y² + 3z² = 9n`, then 3 divides `x`, `y`, and `z`. -/
theorem coordinates_three_dvd_of_represents_nine_mul
    (n x y z : ℤ) (h : x ^ 2 + y ^ 2 + 3 * z ^ 2 = 9 * n) :
    x % 3 = 0 ∧ y % 3 = 0 ∧ z % 3 = 0 := by
  have hxy : (x ^ 2 + y ^ 2) % 3 = 0 := by
    have hm := congrArg (fun t : ℤ => t % 3) h
    norm_num [Int.add_emod, Int.mul_emod] at hm ⊢
    exact hm
  obtain ⟨hx, hy⟩ := RegularReductions.dvd_three_of_sq_add_sq x y hxy
  have hxdiv : 3 * (x / 3) = x := by omega
  have hydiv : 3 * (y / 3) = y := by omega
  have hdiv :
      3 * (x / 3) ^ 2 + 3 * (y / 3) ^ 2 + z ^ 2 = 3 * n := by
    rw [← hxdiv, ← hydiv] at h
    nlinarith
  have hzsq : z ^ 2 % 3 = 0 := by
    have hm := congrArg (fun t : ℤ => t % 3) hdiv
    norm_num [Int.add_emod, Int.mul_emod] at hm ⊢
    exact hm
  have hz0 : 0 ≤ z % 3 := Int.emod_nonneg _ (by norm_num)
  have hz3 : z % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases hz : z % 3
  all_goals norm_num [pow_two, Int.mul_emod, hz] at hzsq
  all_goals norm_num [hx, hy, hz]

/-- `⟨1,1,3⟩` represents `9n` if and only if it represents `n`. -/
theorem represents113_nine_mul_iff (n : ℤ) :
    Represents113 (9 * n) ↔ Represents113 n := by
  constructor
  · rintro ⟨x, y, z, h⟩
    obtain ⟨hx, hy, hz⟩ :=
      coordinates_three_dvd_of_represents_nine_mul n x y z h
    have hxdiv : x = 3 * (x / 3) := by omega
    have hydiv : y = 3 * (y / 3) := by omega
    have hzdiv : z = 3 * (z / 3) := by omega
    refine ⟨x / 3, y / 3, z / 3, ?_⟩
    rw [hxdiv, hydiv, hzdiv] at h
    nlinarith
  · rintro ⟨x, y, z, h⟩
    refine ⟨3 * x, 3 * y, 3 * z, ?_⟩
    nlinarith

/-- `⟨1,1,3⟩` represents `9^a n` if and only if it represents `n`. -/
theorem represents113_nine_pow_mul_iff (n : ℤ) (a : ℕ) :
    Represents113 (9 ^ a * n) ↔ Represents113 n := by
  induction a with
  | zero => simp
  | succ a ih =>
      have he : (9 : ℤ) ^ (a + 1) * n = 9 * (9 ^ a * n) := by
        rw [pow_succ]
        ring
      rw [he, represents113_nine_mul_iff, ih]

/-- `⟨1,1,3⟩` represents no integer `≡ 6 (mod 9)`. -/
theorem not_represents113_mod_nine (n : ℤ) (hn : n % 9 = 6) :
    ¬ Represents113 n := by
  rintro ⟨x, y, z, h⟩
  have hm := congrArg (fun t : ℤ => t % 9) h
  rcases RegularReductions.square_mod_nine x with hx | hx | hx | hx <;>
    rcases RegularReductions.square_mod_nine y with hy | hy | hy | hy <;>
    rcases RegularReductions.square_mod_nine z with hz | hz | hz | hz <;>
    norm_num [Int.add_emod, Int.mul_emod, hx, hy, hz, hn] at hm

/-- `⟨1,1,3⟩` represents no integer `9^a (9b + 6)`. -/
theorem not_represents113_nine_pow (a : ℕ) (b : ℤ) :
    ¬ Represents113 (9 ^ a * (9 * b + 6)) := by
  rw [represents113_nine_pow_mul_iff]
  apply not_represents113_mod_nine
  omega

/-- Every integer represented by `⟨1,1,3⟩` lies outside its exceptional
set. -/
theorem not_exceptional_of_represents113 (n : ℤ) :
    Represents113 n → ¬ Exceptional113 n := by
  intro hrep
  rintro ⟨a, b, rfl⟩
  exact not_represents113_nine_pow a b hrep

/-- Sufficiency for `⟨1,1,3⟩`: every nonnegative integer outside the
exceptional set is represented. `ClassicalInputs.Regular113.Classification` proves it. -/
def Regular113Sufficiency : Prop :=
  ∀ n : ℤ, 0 ≤ n → ¬ Exceptional113 n → Represents113 n

/-- Given sufficiency, a nonnegative integer is represented by `⟨1,1,3⟩` if
and only if it lies outside the exceptional set. -/
theorem criterion_of_sufficiency (h : Regular113Sufficiency)
    (n : ℤ) (hn : 0 ≤ n) :
    Represents113 n ↔ ¬ Exceptional113 n := by
  constructor
  · exact not_exceptional_of_represents113 n
  · exact h n hn

end Regular113

end FibonacciCriterion.ClassicalRepresentation
