import FibonacciCriterion.ClassicalInputs.Reduction.ReducedGram

/-!
# Finite classification of reduced ternary Gram matrices

By `ClassicalInputs.Reduction.ReducedGram`, every positive-definite integral ternary lattice of
determinant `D ≤ 10` has a basis whose Gram matrix lies in an explicit box.
This file enumerates the box (`reducedList D`) and defines a finite
classification (`Classification`): explicit unimodular changes of variables
from each reduced matrix to one of a list of class representatives. A kernel
check of these equivalences gives, for every positive-definite Gram matrix of
determinant `D`, a class representative that represents the same integers
(`Classification.exists_represents_iff_class`).

The classifications at determinants 3, 6, and 10
(`ClassicalInputs.Regular113.Classification`,
`ClassicalInputs.Regular123.Mordell`,
`ClassicalInputs.Regular125.Classification`) and the reduced list at
determinant 7 (`ClassicalInputs.DeterminantSeven.ReducedMatrices`) use this
enumeration.
-/

namespace FibonacciCriterion.TernaryClassification

open TauCeti TernaryGram

/-- The smaller box that the search enumerates, valid for `D ≤ 10`:
`1 ≤ a ≤ 2`, `a ≤ b ≤ 4`, `b ≤ c ≤ 2D`, `abc ≤ 2D`, the reduced off-diagonal
ranges, and `det = D`. -/
def IsBoundedCandidate (D : ℤ) (A : TernaryGram) : Prop :=
  1 ≤ A.a ∧ A.a ≤ 2 ∧ A.a ≤ A.b ∧ A.b ≤ 4 ∧ A.b ≤ A.c ∧ A.c ≤ 2 * D ∧
    A.a * A.b * A.c ≤ 2 * D ∧
    -A.a ≤ 2 * A.r ∧ 2 * A.r ≤ A.a ∧
    -A.a ≤ 2 * A.s ∧ 2 * A.s ≤ A.a ∧
    -A.b ≤ 2 * A.t ∧ 2 * A.t ≤ A.b ∧ A.det = D

instance (D : ℤ) (A : TernaryGram) : Decidable (IsBoundedCandidate D A) := by
  unfold IsBoundedCandidate
  infer_instance

/-- A list of coefficient tuples that contains every matrix of the box at
determinant `D`. -/
def search (D : ℕ) : List TernaryGram :=
  [1, 2].flatMap fun a => [1, 2, 3, 4].flatMap fun b =>
    ((List.range (2 * D)).map fun i : ℕ => (i : ℤ) + 1).flatMap fun c =>
      [-1, 0, 1].flatMap fun r => [-1, 0, 1].flatMap fun s =>
        [-2, -1, 0, 1, 2].map fun t => ⟨a, b, c, r, s, t⟩

/-- The matrices of `search D` in the box at determinant `D`. Every reduced
Gram matrix of determinant `D ≤ 10` is among them. -/
def reducedList (D : ℕ) : List TernaryGram :=
  (search D).filter fun A => decide (IsBoundedCandidate D A)

/-- Every matrix of the box `IsBoundedCandidate D` is in the list `search D`. -/
theorem mem_search_of_bounded {D : ℕ} {A : TernaryGram}
    (h : IsBoundedCandidate D A) : A ∈ search D := by
  rcases A with ⟨a, b, c, r, s, t⟩
  simp only [IsBoundedCandidate] at h
  obtain ⟨ha1, ha2, hab, hb4, hbc, hc, hprod, hrlo, hrhi, hslo, hshi,
    htlo, hthi, hdet⟩ := h
  simp only [search, List.mem_flatMap, List.mem_map]
  refine ⟨a, ?_, b, ?_, c, ⟨(c - 1).toNat, ?_, ?_⟩, r, ?_, s, ?_, t, ?_, rfl⟩
  all_goals first
    | omega
    | (simp only [List.mem_range]; omega)
    | (simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)

/-- Every matrix of the box `IsBoundedCandidate D` is in `reducedList D`. -/
theorem mem_reducedList_of_bounded {D : ℕ} {A : TernaryGram}
    (h : IsBoundedCandidate D A) : A ∈ reducedList D :=
  List.mem_filter.mpr ⟨mem_search_of_bounded h, by simpa using h⟩

/-- For `D ≤ 10`, a Gram matrix in the box `IsBoundedDeterminantCandidate D`
satisfies `IsBoundedCandidate D`: in particular `a ≤ 2` and `b ≤ 4`. -/
theorem isBoundedCandidate_of_isBoundedDeterminantCandidate {D : ℕ} (hD : D ≤ 10)
    {g : TernaryGram} (hg : g.IsBoundedDeterminantCandidate D) :
    IsBoundedCandidate D g := by
  simp only [IsBoundedCandidate]
  rcases hg with ⟨ha, hab, hbc, hc, hx, hy, hz, hprod, hdet⟩
  have hab0 : 0 ≤ g.a * g.b := mul_nonneg ha.le (le_trans ha.le hab)
  have hsize : 2 * g.a * g.b ^ 2 ≤ 4 * (D : ℤ) := by
    have hstep := mul_nonneg hab0 (sub_nonneg.mpr hbc)
    nlinarith
  obtain ⟨ha2, hb4⟩ := small_diagonal_ranges g.a g.b D ha hab
    (by exact_mod_cast hD) hsize
  refine ⟨by omega, ha2, hab, hb4, hbc, hc, hprod, ?_, ?_, ?_, ?_, ?_, ?_, hdet⟩
  · nlinarith [neg_abs_le g.r]
  · nlinarith [le_abs_self g.r]
  · nlinarith [neg_abs_le g.s]
  · nlinarith [le_abs_self g.s]
  · nlinarith [neg_abs_le g.t]
  · nlinarith [le_abs_self g.t]

/-- Every positive-definite Gram matrix of determinant `D ≤ 10` represents
the same integers as some member of `reducedList D`. -/
theorem exists_mem_reducedList_represents_iff (A : TernaryGram)
    (hpos : ∀ x y z : ℤ, x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 → 0 < A.eval x y z)
    {D : ℕ} (hD : D ≤ 10) (hdet : A.det = D) :
    ∃ G ∈ reducedList D, ∀ n : ℤ, A.Represents n ↔ G.Represents n := by
  obtain ⟨b, hb⟩ := exists_basis_isBoundedDeterminantCandidate (tauLattice A)
    (tauLattice_isPosDef A hpos) (tauLattice_finrank A) D
    ((tauLattice_determinant A).trans hdet)
  refine ⟨ofBasis (tauLattice A) b,
    mem_reducedList_of_bounded (isBoundedCandidate_of_isBoundedDeterminantCandidate hD hb), ?_⟩
  intro n
  exact (represents_iff_exists_integralNorm A n).trans
    (represents_ofBasis_iff (tauLattice A) b n).symm

/-- A reduced matrix, a class representative, and a change of variables
between them. -/
structure ReducedEquivalence where
  /-- The reduced Gram matrix. -/
  source : TernaryGram
  /-- The class representative. -/
  target : TernaryGram
  /-- The change of variables `B`; `ReducedEquivalence.Valid` requires
  `Bᵀ source B = target`. -/
  change : Change
deriving DecidableEq

/-- The change of variables `B` has determinant `±1`, `Bᵀ source B = target`,
and the adjugate of `B` carries `target` back to `source` in the same way. -/
def ReducedEquivalence.Valid (e : ReducedEquivalence) : Prop :=
  (e.change.det = 1 ∨ e.change.det = -1) ∧
    e.change.pullback e.source = e.target ∧
    e.change.adjugate.pullback e.target = e.source

instance (e : ReducedEquivalence) : Decidable e.Valid := by
  unfold ReducedEquivalence.Valid
  infer_instance

/-- The source and target of a valid equivalence represent the same
integers. -/
theorem ReducedEquivalence.represents_iff (e : ReducedEquivalence)
    (he : e.Valid) (n : ℤ) :
    e.source.Represents n ↔ e.target.Represents n := by
  constructor
  · intro hn
    rw [← he.2.2] at hn
    exact e.change.adjugate.represents_of_pullback _ hn
  · intro hn
    rw [← he.2.1] at hn
    exact e.change.represents_of_pullback _ hn

/-- A list of class representatives at determinant `D` and a list of
equivalences from the reduced matrices to them. -/
structure Classification (D : ℕ) where
  /-- The class representatives at determinant `D`. -/
  classes : List TernaryGram
  /-- The equivalences; `Classification.Check` requires their sources to be
  the matrices of `reducedList D`, in order. -/
  equivalences : List ReducedEquivalence

/-- The sources of the equivalences are the matrices of `reducedList D`, in
order; each equivalence is valid, and each target is a listed class
representative. -/
def Classification.Check {D : ℕ} (C : Classification D) : Prop :=
  C.equivalences.map ReducedEquivalence.source = reducedList D ∧
    ∀ e ∈ C.equivalences, e.Valid ∧ e.target ∈ C.classes

instance {D : ℕ} (C : Classification D) : Decidable C.Check := by
  unfold Classification.Check
  infer_instance

/-- In a checked classification, every reduced matrix represents the same
integers as one class representative. -/
theorem Classification.exists_class {D : ℕ} {C : Classification D}
    (hC : C.Check) {G : TernaryGram} (hG : G ∈ reducedList D) :
    ∃ T ∈ C.classes, ∀ n : ℤ, G.Represents n ↔ T.Represents n := by
  rw [← hC.1] at hG
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hG
  exact ⟨e.target, (hC.2 e he).2, e.represents_iff (hC.2 e he).1⟩

/-- In a checked classification, every positive-definite Gram matrix of
determinant `D ≤ 10` represents the same integers as one class
representative. -/
theorem Classification.exists_represents_iff_class {D : ℕ} {C : Classification D}
    (hC : C.Check) (hD : D ≤ 10) (A : TernaryGram)
    (hpos : ∀ x y z : ℤ, x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 → 0 < A.eval x y z)
    (hdet : A.det = D) :
    ∃ T ∈ C.classes, ∀ n : ℤ, A.Represents n ↔ T.Represents n := by
  obtain ⟨G, hG, hAG⟩ := exists_mem_reducedList_represents_iff A hpos hD hdet
  obtain ⟨T, hT, hGT⟩ := Classification.exists_class hC hG
  exact ⟨T, hT, fun n => (hAG n).trans (hGT n)⟩

end FibonacciCriterion.TernaryClassification
