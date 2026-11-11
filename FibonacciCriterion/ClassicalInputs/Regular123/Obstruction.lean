import FibonacciCriterion.ClassicalInputs.Representation

/-!
# The obstruction for `⟨1,2,3⟩`

The form `x² + 2y² + 3z²` represents no integer `4^a (16b + 10)`
(`not_represents123_of_exceptional`). As in the manuscript, squares modulo
16 exclude the residue 10, and a factor 4 is removed by descent
(`represents123_four_mul_iff`). If a value is divisible by 4, then either
all three coordinates are even, or `x` and `z` are odd and `y` is even
(`regular123_parity_at_four`). In the second
case the manuscript first applies `X = (x + 3z)/2`, `Z = (x - z)/2`, which
preserves `x² + 3z²`, and then halves all coordinates; here the two steps are
combined into one substitution. No regularity, local–global, or genus theorem
is used.

The converse is proven in `ClassicalInputs.Regular123.Classification`, where
`regular123_criterion` combines the two directions.
-/

namespace FibonacciCriterion.ClassicalRepresentation

open RegularReductions

/-- `⟨1,2,3⟩` represents no integer `≡ 10 (mod 16)`. -/
theorem not_represents123_sixteen_mul_add_ten (b : ℤ) :
    ¬ Represents123 (16 * b + 10) := by
  rintro ⟨x, y, z, h⟩
  have hm := congrArg (fun t : ℤ => t % 16) h
  rcases RegularReductions.square_mod_sixteen x with hx | hx | hx | hx <;>
    rcases RegularReductions.square_mod_sixteen y with hy | hy | hy | hy <;>
    rcases RegularReductions.square_mod_sixteen z with hz | hz | hz | hz <;>
    norm_num [Int.add_emod, Int.mul_emod, hx, hy, hz] at hm

/-- If `x² + 2y² + 3z² = 4n`, then either `x`, `y`, `z` are all even, or `x`
and `z` are odd and `y` is even. -/
theorem regular123_parity_at_four (n x y z : ℤ)
    (h : x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 = 4 * n) :
    (x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0) ∨
      (x % 2 = 1 ∧ y % 2 = 0 ∧ z % 2 = 1) := by
  have hx0 : 0 ≤ x % 4 := Int.emod_nonneg _ (by norm_num)
  have hx4 : x % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hy0 : 0 ≤ y % 4 := Int.emod_nonneg _ (by norm_num)
  have hy4 : y % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hz0 : 0 ≤ z % 4 := Int.emod_nonneg _ (by norm_num)
  have hz4 : z % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hm := congrArg (fun t : ℤ => t % 4) h
  interval_cases hx : x % 4 <;>
    interval_cases hy : y % 4 <;>
    interval_cases hz : z % 4 <;>
    norm_num [pow_two, Int.add_emod, Int.mul_emod, hx, hy, hz] at hm <;>
    omega

/-- `⟨1,2,3⟩` represents `4n` if and only if it represents `n`.

A representation of `4n` need not have all coordinates even. When `x` and `z`
are odd, choose the sign with `x ≡ ±z (mod 4)`; then
`((x ± 3z)/4, y/2, (x ∓ z)/4)` represents `n`. -/
theorem represents123_four_mul_iff (n : ℤ) :
    Represents123 (4 * n) ↔ Represents123 n := by
  constructor
  · rintro ⟨x, y, z, h⟩
    rcases regular123_parity_at_four n x y z h with heven | hodd
    · rcases heven with ⟨hx, hy, hz⟩
      exact ⟨x / 2, y / 2, z / 2, by
        simpa only [one_mul] using diagonal_halve (a := 1) (b := 2) (c := 3) hx hy hz
          (by simpa only [one_mul] using h)⟩
    · rcases hodd with ⟨hx, hy, hz⟩
      have hy' : y = 2 * (y / 2) := by omega
      have hclasses : x % 4 = z % 4 ∨ x % 4 + z % 4 = 4 := by
        have hx0 : 0 ≤ x % 4 := Int.emod_nonneg _ (by norm_num)
        have hx4 : x % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
        have hz0 : 0 ≤ z % 4 := Int.emod_nonneg _ (by norm_num)
        have hz4 : z % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
        omega
      rcases hclasses with hsame | hopp
      · have hplus : (x + 3 * z) % 4 = 0 := by omega
        have hminus : (x - z) % 4 = 0 := by omega
        have hplus' : x + 3 * z = 4 * ((x + 3 * z) / 4) := by omega
        have hminus' : x - z = 4 * ((x - z) / 4) := by omega
        refine ⟨(x + 3 * z) / 4, y / 2, (x - z) / 4, ?_⟩
        nlinarith [congrArg (fun t : ℤ => t ^ 2) hplus',
          congrArg (fun t : ℤ => t ^ 2) hminus',
          congrArg (fun t : ℤ => t ^ 2) hy']
      · have hminus : (x - 3 * z) % 4 = 0 := by omega
        have hplus : (x + z) % 4 = 0 := by omega
        have hminus' : x - 3 * z = 4 * ((x - 3 * z) / 4) := by omega
        have hplus' : x + z = 4 * ((x + z) / 4) := by omega
        refine ⟨(x - 3 * z) / 4, y / 2, (x + z) / 4, ?_⟩
        nlinarith [congrArg (fun t : ℤ => t ^ 2) hminus',
          congrArg (fun t : ℤ => t ^ 2) hplus',
          congrArg (fun t : ℤ => t ^ 2) hy']
  · rintro ⟨x, y, z, h⟩
    refine ⟨2 * x, 2 * y, 2 * z, ?_⟩
    nlinarith

/-- `⟨1,2,3⟩` represents `4^a n` if and only if it represents `n`. -/
theorem represents123_four_pow_mul_iff (n : ℤ) (a : ℕ) :
    Represents123 (4 ^ a * n) ↔ Represents123 n := by
  induction a with
  | zero => simp
  | succ a ih =>
      have he : (4 : ℤ) ^ (a + 1) * n = 4 * (4 ^ a * n) := by
        rw [pow_succ]
        ring
      rw [he, represents123_four_mul_iff, ih]

/-- `⟨1,2,3⟩` represents no member of its exceptional set. -/
theorem not_represents123_of_exceptional {n : ℤ}
    (h : Exceptional123 n) : ¬ Represents123 n := by
  rcases h with ⟨a, b, rfl⟩
  intro hrep
  have hbase : Represents123 (16 * b + 10) :=
    (represents123_four_pow_mul_iff (16 * b + 10) a).1 hrep
  exact not_represents123_sixteen_mul_add_ten b hbase

/-- Every integer represented by `⟨1,2,3⟩` lies outside its exceptional
set. -/
theorem represents123_implies_not_exceptional {n : ℤ}
    (h : Represents123 n) : ¬ Exceptional123 n := by
  intro hex
  exact not_represents123_of_exceptional hex h

end FibonacciCriterion.ClassicalRepresentation
