import FibonacciCriterion.ClassicalInputs.Definitions
import FibonacciCriterion.ClassicalInputs.ThreeSquares.Theorem
import FibonacciCriterion.Fibonacci.Valuations
import FibonacciCriterion.ClassicalInputs.Regular113.Classification
import FibonacciCriterion.ClassicalInputs.Regular123.Classification
import FibonacciCriterion.ClassicalInputs.Regular125.Classification
import FibonacciCriterion.ClassicalInputs.DeterminantSeven

/-!
# Proofs of the classical results

`fibonacciClassicalInputs` fills each field of `FibonacciClassicalInputs` with
a theorem proven in this repository or, for the sufficiency direction of the
three-square theorem, in the pinned dependency atlas-lean. No result about the
criterion is used here.

The imported files give the three-square theorem
(`ClassicalInputs.ThreeSquares.Theorem`), the valuation formulas of Lemma 2.2
(`Fibonacci.Valuations`), the criteria of Proposition 3.2 for `⟨1,1,3⟩`,
`⟨1,2,3⟩`, and `⟨1,2,5⟩` (`ClassicalInputs.Regular113.Classification`,
`ClassicalInputs.Regular123.Classification`,
`ClassicalInputs.Regular125.Classification`), and the sufficiency direction of
Proposition 3.3 (`ClassicalInputs.DeterminantSeven`). The manuscript cites
Jones–Pall for the sufficiency part of the three criteria; here they are
proven by Mordell constructions, and Proposition 3.3 by the manuscript's two
auxiliary-prime constructions. Both use Minkowski reduction (from TauCeti) and
a finite list of reduced Gram matrices.
-/

namespace FibonacciCriterion

open Irregular ClassicalRepresentation

/-- The classical results of `FibonacciClassicalInputs`, proven in this
repository and its pinned dependencies. -/
theorem fibonacciClassicalInputs : FibonacciClassicalInputs where
  representation :=
    { threeSquares_criterion := ClassicalRepresentation.threeSquares_criterion
      regular113_criterion := MordellRegularity.regular113_criterion
      regular123_criterion := Regular123.regular123_criterion
      regular125_criterion := Mordell125.regular125_criterion
      eligible_f_or_h := DeterminantSevenGenus.eligible_f_or_h }
  valuations := fibonacciValuationInputs

end FibonacciCriterion
