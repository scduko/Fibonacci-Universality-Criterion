import FibonacciCriterion.Irregular.Forms
import FibonacciCriterion.ClassicalInputs.Reduction.Classification

/-!
# The reduced Gram matrices of determinant 7

In the proof of Proposition 3.3, Minkowski reduction leaves finitely many Gram
matrices of determinant 7. The box of
`ClassicalInputs.Reduction.Classification` contains fifteen of them
(`reducedDetSeven`): `h`, `f` with either sign of its off-diagonal entry
(`Irregular.hGram`, `Irregular.fGram`), and twelve matrices with diagonal
`(2, 2, 3)`. A kernel check over 5,040 coefficient tuples confirms the list
(`reducedList_seven`).

The manuscript shows that the last twelve are equivalent to a third lattice
`K₇`; here they are excluded by the number of zeros modulo 7
(`ClassicalInputs.DeterminantSeven.ZeroCount`) and are never compared with `K₇`.
-/

namespace FibonacciCriterion.DeterminantSevenGenus

/-- The fifteen Gram matrices of determinant 7 in the box, written
`⟨a, b, c, r, s, t⟩`. -/
def reducedDetSeven : List TernaryGram :=
  [⟨1, 1, 7, 0, 0, 0⟩,
   ⟨1, 2, 4, 0, 0, -1⟩,
   ⟨1, 2, 4, 0, 0, 1⟩,
   ⟨2, 2, 3, -1, -1, 0⟩,
   ⟨2, 2, 3, -1, -1, 1⟩,
   ⟨2, 2, 3, -1, 0, -1⟩,
   ⟨2, 2, 3, -1, 0, 1⟩,
   ⟨2, 2, 3, -1, 1, -1⟩,
   ⟨2, 2, 3, -1, 1, 0⟩,
   ⟨2, 2, 3, 1, -1, -1⟩,
   ⟨2, 2, 3, 1, -1, 0⟩,
   ⟨2, 2, 3, 1, 0, -1⟩,
   ⟨2, 2, 3, 1, 0, 1⟩,
   ⟨2, 2, 3, 1, 1, 0⟩,
   ⟨2, 2, 3, 1, 1, 1⟩]

set_option maxRecDepth 100000 in
/-- The matrices of determinant 7 in the box are the fifteen matrices of
`reducedDetSeven`. -/
theorem reducedList_seven : TernaryClassification.reducedList 7 = reducedDetSeven := by
  decide +kernel

end FibonacciCriterion.DeterminantSevenGenus
