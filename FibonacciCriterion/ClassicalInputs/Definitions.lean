import FibonacciCriterion.ClassicalInputs.Representation
import FibonacciCriterion.Fibonacci.ValuationInputs

/-!
# The classical results used by the proof

The structure `FibonacciClassicalInputs` collects the classical results that
the proof of the criterion uses:

1. the Gauss–Legendre three-square theorem;
2. the criteria of Proposition 3.2 for `⟨1,1,3⟩`, `⟨1,2,3⟩`, and `⟨1,2,5⟩`;
3. the sufficiency direction of Proposition 3.3: every eligible positive
   integer not divisible by 49 is represented by `f` or `h`; and
4. the Fibonacci valuation formulas of Lemma 2.2 at 2, 3, and 5.

The proof of the criterion in `FibonacciCriterion.Criterion.Proof` takes these
results as a hypothesis. `FibonacciCriterion.ClassicalInputs.Theorems` proves
them.
-/

namespace FibonacciCriterion

/-- The classical results used by the proof of the criterion: the
representation theorems of Propositions 3.2 and 3.3
(`ClassicalRepresentation.Inputs`) and the valuation formulas of Lemma 2.2
(`FibonacciValuationInputs`). -/
structure FibonacciClassicalInputs : Prop where
  /-- The three-square theorem, the criteria of Proposition 3.2, and the
  sufficiency direction of Proposition 3.3. -/
  representation : ClassicalRepresentation.Inputs
  /-- The valuation formulas of Lemma 2.2 at 2, 3, and 5. -/
  valuations : FibonacciValuationInputs

end FibonacciCriterion
