import MathlibExt.NumberTheory.QuadraticForms.LegendreThreeSquare
import FibonacciCriterion.ClassicalInputs.Representation
import FibonacciCriterion.ClassicalInputs.ThreeSquares.Obstruction

/-!
# The Gauss–Legendre three-square theorem

`threeSquares_criterion` is the three-square theorem over the integers, the
row of Proposition 3.2 for `⟨1,1,1⟩`. Sufficiency is the natural-number
theorem `Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven` of
the pinned atlas-lean dependency (imported under `MathlibExt`); necessity is
`not_threeSquares_four_pow`. The hypothesis `0 ≤ n` is needed: no negative
integer is a sum of squares, but some lie outside the exceptional set.
-/

namespace FibonacciCriterion.ClassicalRepresentation

open RegularReductions

/-- Proposition 3.2 for `⟨1,1,1⟩` (the Gauss–Legendre three-square theorem):
a nonnegative integer `n` is a sum of three squares if and only if `n` is not
of the form `4^a (8b + 7)`. -/
theorem threeSquares_criterion (n : ℤ) (hn : 0 ≤ n) :
    ThreeSquares n ↔ ¬ ThreeSquareExceptional n := by
  constructor
  · intro hrep hex
    rcases hex with ⟨a, b, rfl⟩
    exact (not_threeSquares_four_pow a b) hrep
  · intro hnot
    let m : ℕ := n.toNat
    have hmn : (m : ℤ) = n := by
      simpa [m] using Int.toNat_of_nonneg hn
    have hnotNat : ¬ ∃ a b : ℕ, m = 4 ^ a * (8 * b + 7) := by
      rintro ⟨a, b, hab⟩
      apply hnot
      refine ⟨a, (b : ℤ), ?_⟩
      rw [← hmn]
      exact_mod_cast hab
    obtain ⟨x, y, z, hxyz⟩ :=
      Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven m hnotNat
    refine ⟨(x : ℤ), (y : ℤ), (z : ℤ), ?_⟩
    rw [← hmn]
    exact_mod_cast hxyz

end FibonacciCriterion.ClassicalRepresentation
