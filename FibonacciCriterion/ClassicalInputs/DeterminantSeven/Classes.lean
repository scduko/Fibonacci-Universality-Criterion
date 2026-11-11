import FibonacciCriterion.ClassicalInputs.DeterminantSeven.ReducedMatrices

/-!
# The reduced Gram matrices in the classes of `f` and `h`

Of the fifteen reduced Gram matrices of determinant 7
(`ClassicalInputs.DeterminantSeven.ReducedMatrices`), three lie in the classes
of `f` and `h`: `h`, and `f` with either sign of its off-diagonal entry
(`reducedFHGenus`). An integer represented by one of them is represented by
`f` or `h` (`represents_of_reducedFHGenus`).
-/

namespace FibonacciCriterion.DeterminantSevenGenus

/-- The three reduced Gram matrices in the classes of `f` and `h`: `h`, and
`f` with either sign of `t`. Both signs occur in `reducedDetSeven`. -/
def reducedFHGenus : List TernaryGram :=
  [⟨1, 1, 7, 0, 0, 0⟩,
   ⟨1, 2, 4, 0, 0, -1⟩,
   ⟨1, 2, 4, 0, 0, 1⟩]

/-- An integer represented by a matrix of `reducedFHGenus` is represented by
`h` or by `f`. -/
theorem represents_of_reducedFHGenus (A : TernaryGram) (n : ℤ)
    (hA : A ∈ reducedFHGenus) (hn : A.Represents n) :
    Irregular.hGram.Represents n ∨ Irregular.fGram.Represents n := by
  simp only [reducedFHGenus, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl
  · exact Or.inl hn
  · right
    let B : Change := ⟨-1, 0, 0, 0, -1, -1, 0, 0, -1⟩
    let C := B.adjugate
    have hpb : C.pullback Irregular.fGram = ⟨1, 2, 4, 0, 0, -1⟩ := by decide
    rcases hn with ⟨x, y, z, hxyz⟩
    refine ⟨C.m11 * x + C.m12 * y + C.m13 * z,
      C.m21 * x + C.m22 * y + C.m23 * z,
      C.m31 * x + C.m32 * y + C.m33 * z, ?_⟩
    rw [← C.pullback_eval, hpb]
    exact hxyz
  · exact Or.inr hn

end FibonacciCriterion.DeterminantSevenGenus
