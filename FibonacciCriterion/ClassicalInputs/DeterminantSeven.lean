import FibonacciCriterion.ClassicalInputs.DeterminantSeven.Unramified
import FibonacciCriterion.ClassicalInputs.DeterminantSeven.Ramified

/-!
# Representation by `f` or `h` (Proposition 3.3)

`eligible_f_or_h` proves the sufficiency direction of Proposition 3.3 for
integers not divisible by 49: every `ResidualEligible` integer is represented
by `f` or `h`. This file does not import the proof of the criterion.

The auxiliary-prime constructions of the two cases of the manuscript's proof,
`7 ∤ n` (called unramified here) and `n = 7u` (ramified), give a positive-definite
Gram matrix of determinant 7 that represents the integer and has
seven zeros modulo 7. Minkowski reduction and the finite list of
reduced Gram matrices of determinant 7 then give representation by `f` or
`h`.
-/

namespace FibonacciCriterion.DeterminantSevenGenus

/-- Every `ResidualEligible` integer `n` has an auxiliary-prime witness: an
unramified one if `7 ∤ n` and a ramified one if `7 ∣ n`. -/
theorem sevenArithmetic : SevenArithmetic :=
  sevenArithmetic_of_cases
    unramifiedSevenArithmetic ramifiedSevenArithmetic

/-- Every `ResidualEligible` integer is represented by a positive-definite
Gram matrix of determinant 7 with seven zeros modulo 7. -/
theorem sevenGramConstruction : SevenGramConstruction :=
  sevenGramConstruction_of_arithmetic sevenArithmetic

/-- Proposition 3.3, sufficiency direction: every eligible positive integer
not divisible by 49 is represented by `f` or `h`. -/
theorem eligible_f_or_h
    (n : ℕ) (hn : Irregular.ResidualEligible n) :
    Irregular.RepresentsF (n : ℤ) ∨
      Irregular.RepresentsH (n : ℤ) :=
  eligible_f_or_h_of_gramConstruction sevenGramConstruction n hn

end FibonacciCriterion.DeterminantSevenGenus
