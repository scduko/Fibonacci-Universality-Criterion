import FibonacciCriterion.ClassicalInputs.Regular113.Mordell
import FibonacciCriterion.ClassicalInputs.Reduction.Classification

/-!
# The determinant-3 classification and the criterion for `⟨1,1,3⟩`

This file proves `DeterminantThreeClassification`, the classification
hypothesis of `ClassicalInputs.Regular113.Mordell`. TauCeti's Minkowski
reduction and the kernel-checked list `detThree` show that every positive-definite
integral ternary form of determinant 3 represents the same integers
as `⟨1,1,3⟩` or as the Gram matrix `⟨1, 2, 2, 0, 0, -1⟩`, which is `Q113Other`
after `z ↦ -z`.

With the classification, `regular113_criterion` is the criterion of
Proposition 3.2 for `⟨1,1,3⟩`.
-/

namespace FibonacciCriterion.MordellRegularity

/-- The classification at determinant 3: the classes `⟨1,1,3⟩` and
`x² + 2y² + 2z² - 2yz`, with explicit equivalences from every reduced Gram
matrix. -/
def detThree : TernaryClassification.Classification 3 where
  classes := [⟨1, 1, 3, 0, 0, 0⟩, ⟨1, 2, 2, 0, 0, -1⟩]
  equivalences :=
    [⟨⟨1, 1, 3, 0, 0, 0⟩, ⟨1, 1, 3, 0, 0, 0⟩, ⟨-1, 0, 0, 0, -1, 0, 0, 0, -1⟩⟩,
     ⟨⟨1, 2, 2, 0, 0, -1⟩, ⟨1, 2, 2, 0, 0, -1⟩, ⟨-1, 0, 0, 0, -1, 0, 0, 0, -1⟩⟩,
     ⟨⟨1, 2, 2, 0, 0, 1⟩, ⟨1, 2, 2, 0, 0, -1⟩, ⟨-1, 0, 0, 0, -1, 0, 0, 0, 1⟩⟩]

set_option maxRecDepth 100000 in
/-- Kernel check of `detThree`: the sources of its equivalences are the matrices of
`reducedList 3`, in order; each change of variables is unimodular and carries
its source to its target; and each target is a listed class representative. -/
theorem detThree_check : detThree.Check := by
  decide +kernel

/-- The Gram matrix `⟨1, 2, 2, 0, 0, -1⟩` and `Q113Other` represent the same
integers, by `z ↦ -z`. -/
theorem otherClass_represents_iff (n : ℤ) :
    (⟨1, 2, 2, 0, 0, -1⟩ : TernaryGram).Represents n ↔
      Represents Q113Other n := by
  constructor
  · rintro ⟨x, y, z, h⟩
    refine ⟨x, y, -z, ?_⟩
    calc
      Q113Other x y (-z) =
          (⟨1, 2, 2, 0, 0, -1⟩ : TernaryGram).eval x y z := by
        simp only [Q113Other, TernaryGram.eval]
        ring
      _ = n := h
  · rintro ⟨x, y, z, h⟩
    refine ⟨x, y, -z, ?_⟩
    calc
      (⟨1, 2, 2, 0, 0, -1⟩ : TernaryGram).eval x y (-z) =
          Q113Other x y z := by
        simp only [Q113Other, TernaryGram.eval]
        ring
      _ = n := h

/-- Every positive Mordell form of determinant 3 represents the same
integers as `Q113` or `Q113Other`. -/
theorem determinantThreeClassification : DeterminantThreeClassification := by
  intro m hm d hpos
  obtain ⟨T, hT, hrep⟩ := TernaryClassification.Classification.exists_represents_iff_class
    detThree_check (by norm_num) d.ternaryGram
      (by
        intro x y z hne
        rw [d.ternaryGram_eval]
        exact hpos x y z hne)
      (by rw [d.ternaryGram_det hm]; norm_num)
  simp only [detThree, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · left
    intro n
    have h := (d.ternaryGram_represents_iff n).symm.trans (hrep n)
    simpa only [TernaryGram.Represents, TernaryGram.eval, Represents, Q113, one_mul,
      zero_mul, mul_zero, add_zero] using h
  · right
    intro n
    exact (d.ternaryGram_represents_iff n).symm.trans
      ((hrep n).trans (otherClass_represents_iff n))

/-- Sufficiency for `⟨1,1,3⟩`: every nonnegative integer outside the
exceptional set is represented. The manuscript cites Jones–Pall; here the
proof uses the Mordell construction and the classification at
determinant 3. -/
theorem regular113Sufficiency : ClassicalRepresentation.Regular113.Regular113Sufficiency :=
  regular113Sufficiency_of_classification determinantThreeClassification

/-- Proposition 3.2 for `⟨1,1,3⟩`: a nonnegative integer `n` is represented
by `⟨1,1,3⟩` if and only if `n` is not of the form `9^a (9b + 6)`. -/
theorem regular113_criterion (n : ℤ) (hn : 0 ≤ n) :
    ClassicalRepresentation.Represents113 n ↔
      ¬ ClassicalRepresentation.Exceptional113 n :=
  ClassicalRepresentation.Regular113.criterion_of_sufficiency regular113Sufficiency n hn

end FibonacciCriterion.MordellRegularity
