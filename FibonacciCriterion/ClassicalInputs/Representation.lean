import FibonacciCriterion.ClassicalInputs.ThreeSquares.Scaling
import FibonacciCriterion.Irregular.Eligibility

/-!
# The classical representation theorems used by the proof

The structure `ClassicalRepresentation.Inputs` collects the classical
representation theorems that the proof of the criterion uses. The proof takes
a value of `Inputs` as a hypothesis; `ClassicalInputs.Theorems` constructs one
from proofs in this repository and its pinned dependencies.

The first four fields are the criteria of Proposition 3.2 for the regular
ternaries `⟨1,1,1⟩`, `⟨1,1,3⟩`, `⟨1,2,3⟩`, and `⟨1,2,5⟩`. The last field is the
sufficiency direction of Proposition 3.3 for `f` and `h`. The reductions of
`⟨1,1,2⟩`, `⟨1,2,2⟩`, and `⟨1,2,4⟩` to sums of three squares are in
`ClassicalInputs.ThreeSquares.Reductions`,
`ClassicalInputs.ThreeSquares.DiagonalReductions`, and
`ClassicalInputs.ThreeSquares.Scaling`. This file derives the criterion for
`⟨1,1,2⟩` from the three-square theorem
(`Inputs.represents112_iff_not_exceptional`) and proves that `g` and `⟨1,1,1⟩`
represent the same integers (`Inputs.representsG_iff_threeSquares`, which does
not use the inputs). The criteria for `⟨1,2,2⟩`, `g`, and `⟨1,2,4⟩` are
`TwoAdic.represents122_iff`, `TwoAdic.representsG_iff`, and
`TwoAdic.represents124_iff` in `Regular.TwoAdicEscalators`.
-/

namespace FibonacciCriterion

open Irregular

namespace ClassicalRepresentation

/-- The integers `4^a (8b + 7)`, the exceptional set of the three-square
theorem. -/
def ThreeSquareExceptional (n : ℤ) : Prop :=
  ∃ a : ℕ, ∃ b : ℤ, n = 4 ^ a * (8 * b + 7)

/-- The integers `4^a (16b + 14)`, the exceptional set of `⟨1,1,2⟩` and
`⟨1,2,4⟩`. -/
def Exceptional112 (n : ℤ) : Prop :=
  ∃ a : ℕ, ∃ b : ℤ, n = 4 ^ a * (16 * b + 14)

/-- Representation of `n` by the diagonal form `⟨1,1,3⟩`. -/
def Represents113 (n : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 3 * z ^ 2 = n

/-- The integers `9^a (9b + 6)`, the exceptional set of `⟨1,1,3⟩`. -/
def Exceptional113 (n : ℤ) : Prop :=
  ∃ a : ℕ, ∃ b : ℤ, n = 9 ^ a * (9 * b + 6)

/-- Representation of `n` by the diagonal form `⟨1,2,3⟩`. -/
def Represents123 (n : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 = n

/-- The integers `4^a (16b + 10)`, the exceptional set of `⟨1,2,3⟩`. -/
def Exceptional123 (n : ℤ) : Prop :=
  ∃ a : ℕ, ∃ b : ℤ, n = 4 ^ a * (16 * b + 10)

/-- Representation of `n` by the diagonal form `⟨1,2,5⟩`. -/
def Represents125 (n : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + 2 * y ^ 2 + 5 * z ^ 2 = n

/-- The integers `5 · 25^a (5b + r)` with `r ∈ {2, 3}`, the exceptional set of
`⟨1,2,5⟩`. -/
def Exceptional125 (n : ℤ) : Prop :=
  ∃ a : ℕ, ∃ b r : ℤ,
    (r = 2 ∨ r = 3) ∧ n = 5 * 25 ^ a * (5 * b + r)

/-- Representation of `n` by the escalator `g = x² + 2y² + 2yz + 5z²` of
determinant 9. -/
def RepresentsG (n : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + 2 * y ^ 2 + 2 * y * z + 5 * z ^ 2 = n

/-- The five classical representation theorems used by the proof: the
criteria of Proposition 3.2 for `⟨1,1,1⟩`, `⟨1,1,3⟩`, `⟨1,2,3⟩`, and
`⟨1,2,5⟩`, and the sufficiency direction of Proposition 3.3.

The criteria are stated for nonnegative integers, the only range the proof
uses. The last field is stated for eligible integers not divisible by 49
(`ResidualEligible`). Of its applications, only Proposition 6.2 meets multiples
of 49, and its induction scales a representation by `f ⊥ ⟨7⟩` by 7. -/
structure Inputs : Prop where
  threeSquares_criterion : ∀ n : ℤ, 0 ≤ n →
    (RegularReductions.ThreeSquares n ↔ ¬ ThreeSquareExceptional n)
  regular113_criterion : ∀ n : ℤ, 0 ≤ n →
    (Represents113 n ↔ ¬ Exceptional113 n)
  regular123_criterion : ∀ n : ℤ, 0 ≤ n →
    (Represents123 n ↔ ¬ Exceptional123 n)
  regular125_criterion : ∀ n : ℤ, 0 ≤ n →
    (Represents125 n ↔ ¬ Exceptional125 n)
  eligible_f_or_h : ∀ n : ℕ, ResidualEligible n →
    RepresentsF (n : ℤ) ∨ RepresentsH (n : ℤ)

namespace Inputs

variable (c : Inputs)
include c

omit c in
/-- `2n` lies in the exceptional set of the three-square theorem if and only
if `n` lies in the exceptional set of `⟨1,1,2⟩`. -/
theorem threeSquareExceptional_twice_iff (n : ℤ) :
    ThreeSquareExceptional (2 * n) ↔ Exceptional112 n := by
  constructor
  · rintro ⟨a, b, hab⟩
    cases a with
    | zero =>
        simp only [pow_zero, one_mul] at hab
        omega
    | succ a =>
        refine ⟨a, b, ?_⟩
        rw [pow_succ] at hab
        nlinarith
  · rintro ⟨a, b, hab⟩
    refine ⟨a + 1, b, ?_⟩
    rw [hab, pow_succ]
    ring

/-- Proposition 3.2 for `⟨1,1,2⟩`: a nonnegative integer `n` is represented by
`⟨1,1,2⟩` if and only if it is not of the form `4^a (16b + 14)`. The proof
applies the three-square theorem to `2n`. -/
theorem represents112_iff_not_exceptional (n : ℤ) (hn : 0 ≤ n) :
    RegularReductions.Represents112 n ↔ ¬ Exceptional112 n := by
  rw [RegularReductions.represents112_iff_threeSquares_twice,
    ClassicalRepresentation.Inputs.threeSquares_criterion c
      (2 * n) (by omega),
    threeSquareExceptional_twice_iff]

omit c in
/-- If `n = x² + a² + b²` with `a ≡ b (mod 3)`, then `g` represents `n`: the
integers `y = (a + 2b)/3` and `z = (a - b)/3` satisfy `a = y + 2z` and
`b = y - z`. -/
theorem representsG_of_congruent_pair (n x a b : ℤ)
    (hab : a % 3 = b % 3) (h : x ^ 2 + a ^ 2 + b ^ 2 = n) :
    RepresentsG n := by
  have hsum : 3 * ((a + 2 * b) / 3) = a + 2 * b := by omega
  have hdiff : 3 * ((a - b) / 3) = a - b := by omega
  let y := (a + 2 * b) / 3
  let z := (a - b) / 3
  have ha : a = y + 2 * z := by
    dsimp [y, z]
    omega
  have hb : b = y - z := by
    dsimp [y, z]
    omega
  refine ⟨x, y, z, ?_⟩
  nlinarith [congrArg (fun t : ℤ => t ^ 2) ha,
    congrArg (fun t : ℤ => t ^ 2) hb]

omit c in
/-- The escalator `g` represents the same integers as `⟨1,1,1⟩` (part of
Proposition 3.2). One direction is the identity
`g(x, y, z) = x² + (y + 2z)² + (y - z)²`. For the other, as in the manuscript,
two of the three coordinates are congruent modulo 3 after a change of sign. -/
theorem representsG_iff_threeSquares (n : ℤ) :
    RepresentsG n ↔ RegularReductions.ThreeSquares n := by
  constructor
  · rintro ⟨x, y, z, h⟩
    refine ⟨x, y + 2 * z, y - z, ?_⟩
    nlinarith
  · rintro ⟨x, y, z, h⟩
    have hxr : 0 ≤ x % 3 ∧ x % 3 < 3 :=
      ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    have hyr : 0 ≤ y % 3 ∧ y % 3 < 3 :=
      ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    have hzr : 0 ≤ z % 3 ∧ z % 3 < 3 :=
      ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    have hp :
        x % 3 = y % 3 ∨ x % 3 + y % 3 = 3 ∨
        x % 3 = z % 3 ∨ x % 3 + z % 3 = 3 ∨
        y % 3 = z % 3 ∨ y % 3 + z % 3 = 3 := by
      omega
    rcases hp with hxy | hxy | hxz | hxz | hyz | hyz
    · exact representsG_of_congruent_pair n z x y hxy (by nlinarith)
    · apply representsG_of_congruent_pair n z x (-y) (by omega)
      nlinarith
    · exact representsG_of_congruent_pair n y x z hxz (by nlinarith)
    · apply representsG_of_congruent_pair n y x (-z) (by omega)
      nlinarith
    · exact representsG_of_congruent_pair n x y z hyz h
    · apply representsG_of_congruent_pair n x y (-z) (by omega)
      nlinarith

end Inputs
end ClassicalRepresentation

/-- Short name for `ClassicalRepresentation.Inputs`, the representation
theorems only. The full set of classical results, with the valuation formulas,
is `FibonacciClassicalInputs`. -/
abbrev ClassicalInputs := ClassicalRepresentation.Inputs

end FibonacciCriterion
