import FibonacciCriterion.ClassicalInputs.Regular125.Mordell
import FibonacciCriterion.ClassicalInputs.Reduction.Classification

/-!
# The determinant-10 classification and the criterion for `⟨1,2,5⟩`

This file proves `DeterminantTenClassification`, the classification
hypothesis of `ClassicalInputs.Regular125.Mordell`. TauCeti's Minkowski
reduction and the kernel-checked list `detTen` show that every positive-definite
integral ternary form of determinant 10 represents the same integers
as one of four class representatives, one of them even-valued. Positivity of
the Mordell form comes from `MordellDatum.positive_of_determinant_pos`.

With the classification, `regular125Sufficiency` proves sufficiency for
`⟨1,2,5⟩`, and `regular125_criterion` is the criterion of Proposition 3.2.
-/

namespace FibonacciCriterion.Mordell125

/-- The classification at determinant 10: four classes, one of them
even-valued, with explicit equivalences from every reduced Gram matrix. -/
def detTen : TernaryClassification.Classification 10 where
  classes := [⟨1, 2, 5, 0, 0, 0⟩, ⟨2, 2, 3, 0, 1, 0⟩, ⟨1, 1, 10, 0, 0, 0⟩,
    ⟨2, 2, 4, -1, -1, 0⟩]
  equivalences :=
    [⟨⟨1, 1, 10, 0, 0, 0⟩, ⟨1, 1, 10, 0, 0, 0⟩, ⟨-1, 0, 0, 0, -1, 0, 0, 0, -1⟩⟩,
     ⟨⟨1, 2, 5, 0, 0, 0⟩, ⟨1, 2, 5, 0, 0, 0⟩, ⟨-1, 0, 0, 0, -1, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 3, 0, -1, 0⟩, ⟨2, 2, 3, 0, 1, 0⟩, ⟨-1, 0, 0, 0, -1, 0, 0, 0, 1⟩⟩,
     ⟨⟨2, 2, 3, 0, 0, -1⟩, ⟨2, 2, 3, 0, 1, 0⟩, ⟨0, -1, 0, -1, 0, 0, 0, 0, 1⟩⟩,
     ⟨⟨2, 2, 3, 0, 0, 1⟩, ⟨2, 2, 3, 0, 1, 0⟩, ⟨0, -1, 0, -1, 0, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 3, 0, 1, 0⟩, ⟨2, 2, 3, 0, 1, 0⟩, ⟨-1, 0, 0, 0, -1, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 4, -1, -1, 0⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨-1, 0, 0, 0, -1, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 4, -1, -1, 1⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨-1, 0, 1, -1, 1, 0, 0, 0, 1⟩⟩,
     ⟨⟨2, 2, 4, -1, 0, -1⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨0, -1, 0, -1, 0, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 4, -1, 0, 1⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨0, -1, 0, -1, 0, 0, 0, 0, 1⟩⟩,
     ⟨⟨2, 2, 4, -1, 1, -1⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨-1, 0, 1, -1, 1, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 4, -1, 1, 0⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨-1, 0, 0, 0, -1, 0, 0, 0, 1⟩⟩,
     ⟨⟨2, 2, 4, 1, -1, -1⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨-1, 0, 1, 0, 1, 0, 0, 0, 1⟩⟩,
     ⟨⟨2, 2, 4, 1, -1, 0⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨-1, 0, 0, 0, 1, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 4, 1, 0, -1⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨0, 1, 0, -1, 0, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 4, 1, 0, 1⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨0, 1, 0, -1, 0, 0, 0, 0, 1⟩⟩,
     ⟨⟨2, 2, 4, 1, 1, 0⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨-1, 0, 0, 0, 1, 0, 0, 0, 1⟩⟩,
     ⟨⟨2, 2, 4, 1, 1, 1⟩, ⟨2, 2, 4, -1, -1, 0⟩, ⟨-1, 0, 1, 0, 1, 0, 0, 0, -1⟩⟩]

set_option maxRecDepth 100000 in
/-- Kernel check of `detTen`: the sources of its equivalences are the matrices of
`reducedList 10`, in order; each change of variables is unimodular and carries
its source to its target; and each target is a listed class representative. -/
theorem detTen_check : detTen.Check := by
  decide +kernel

/-- The four class representatives evaluate to the polynomials of
`Represents125`, `RepresentsQ2`, `RepresentsQ3`, and `RepresentsQ4`, so they
represent the same integers. -/
theorem detTen_classes_represents_iff (n : ℤ) :
    ((⟨1, 2, 5, 0, 0, 0⟩ : TernaryGram).Represents n ↔
        ClassicalRepresentation.Represents125 n) ∧
      ((⟨2, 2, 3, 0, 1, 0⟩ : TernaryGram).Represents n ↔ RepresentsQ2 n) ∧
      ((⟨1, 1, 10, 0, 0, 0⟩ : TernaryGram).Represents n ↔ RepresentsQ3 n) ∧
      ((⟨2, 2, 4, -1, -1, 0⟩ : TernaryGram).Represents n ↔ RepresentsQ4 n) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    constructor <;>
    rintro ⟨x, y, z, h⟩ <;>
    refine ⟨x, y, z, ?_⟩ <;>
    simp only [TernaryGram.eval] at h ⊢ <;>
    convert h using 1 <;> ring

/-- Every positive Mordell form of determinant 10 represents the same
integers as one of the four classes. Positivity and the determinant come from
the datum (`MordellDatum.positive_of_determinant_pos`,
`MordellDatum.ternaryGram_det`). -/
theorem determinantTenClassification : DeterminantTenClassification := by
  intro m d hm ha
  obtain ⟨T, hT, hrep⟩ := TernaryClassification.Classification.exists_represents_iff_class
    detTen_check (by norm_num) d.ternaryGram
      (by
        intro x y z hne
        rw [d.ternaryGram_eval]
        exact d.positive_of_determinant_pos hm (by norm_num) ha x y z hne)
      (by rw [d.ternaryGram_det (ne_of_gt hm)]; norm_num)
  have hd (n : ℤ) : d.Represents n ↔ T.Represents n :=
    (d.ternaryGram_represents_iff n).symm.trans (hrep n)
  simp only [detTen, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact Or.inl fun n => (hd n).trans (detTen_classes_represents_iff n).1
  · exact Or.inr (Or.inl fun n => (hd n).trans (detTen_classes_represents_iff n).2.1)
  · exact Or.inr (Or.inr (Or.inl fun n =>
      (hd n).trans (detTen_classes_represents_iff n).2.2.1))
  · exact Or.inr (Or.inr (Or.inr fun n =>
      (hd n).trans (detTen_classes_represents_iff n).2.2.2))

/-- Proposition 3.2 for `⟨1,2,5⟩`, sufficiency: every nonnegative integer
outside the exceptional set is represented by `⟨1,2,5⟩`. The manuscript cites
Jones–Pall; here the proof uses the Mordell construction and the
classification at determinant 10. -/
theorem regular125Sufficiency : FibonacciCriterion.Regular125Sufficiency :=
  regular125Sufficiency_of_classification determinantTenClassification

/-- Proposition 3.2 for `⟨1,2,5⟩`: a nonnegative integer `n` is represented by
`⟨1,2,5⟩` if and only if `n` is not of the form `5 · 25^a (5b + r)` with
`r ∈ {2, 3}`. -/
theorem regular125_criterion (n : ℤ) (hn : 0 ≤ n) :
    ClassicalRepresentation.Represents125 n ↔
      ¬ ClassicalRepresentation.Exceptional125 n :=
  regular125_criterion_of_sufficiency regular125Sufficiency n hn

end FibonacciCriterion.Mordell125
