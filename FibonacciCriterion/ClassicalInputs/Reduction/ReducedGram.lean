import FibonacciCriterion.Forms
import Mathlib.LinearAlgebra.Basis.Basic
import FibonacciCriterion.ClassicalInputs.Reduction.Bounds
import FibonacciCriterion.ClassicalInputs.Reduction.Lattice
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.ReducedGram

/-!
# Minkowski-reduced ternary Gram matrices

TauCeti supplies a Minkowski-reduced basis of a positive-definite lattice.
This file derives the bounds on the Gram matrix of such a basis, for a
`TernaryGram` with matrix

```
       [ a  r  s ]
  G =  [ r  b  t ].
       [ s  t  c ]
```

A reduced basis of a ternary lattice of determinant `D` has Gram matrix in an
explicit box (`IsBoundedDeterminantCandidate`,
`exists_basis_isBoundedDeterminantCandidate`), which includes Mahler's bound
`abc ≤ 2D`. The manuscript cites Mahler for this bound; here it is proven
(`product_le_two_mul_determinant`). For `D ≤ 10`,
`ClassicalInputs.Reduction.Classification` places this box inside the smaller
box `TernaryClassification.IsBoundedCandidate` (`a ≤ 2`, `b ≤ 4`) and enumerates
that.
-/

namespace FibonacciCriterion

open TauCeti
open scoped Matrix

namespace TernaryGram

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The size inequalities of a Minkowski-reduced ternary basis:
`0 < a ≤ b ≤ c`, `2|r| ≤ a`, `2|s| ≤ a`, and `2|t| ≤ b`. -/
def HasMinkowskiBounds (g : TernaryGram) : Prop :=
  0 < g.a ∧ g.a ≤ g.b ∧ g.b ≤ g.c ∧
    2 * |g.r| ≤ g.a ∧ 2 * |g.s| ≤ g.a ∧ 2 * |g.t| ≤ g.b

/-- The four inequalities `N(b₂) ≤ N(b₂ ± b₀ ± b₁)` of a Minkowski-reduced
ternary basis `b₀, b₁, b₂`, in terms of the coefficients:
`0 ≤ a + b ± 2r ± 2s ± 2t` with an even number of minus signs. -/
def HasSignSumBounds (g : TernaryGram) : Prop :=
  0 ≤ g.a + g.b + 2 * g.r + 2 * g.s + 2 * g.t ∧
  0 ≤ g.a + g.b + 2 * g.r - 2 * g.s - 2 * g.t ∧
  0 ≤ g.a + g.b - 2 * g.r + 2 * g.s - 2 * g.t ∧
  0 ≤ g.a + g.b - 2 * g.r - 2 * g.s + 2 * g.t

/-- The Gram matrix of a Minkowski-reduced basis of a positive-definite
ternary lattice satisfies `HasMinkowskiBounds`. -/
theorem hasMinkowskiBounds_of_isMinkowskiReduced
    (L : IntegralLattice V) (hL : L.IsPosDef)
    (b : Module.Basis (Fin 3) ℤ L) (hb : L.IsMinkowskiReduced b) :
    (ofBasis L b).HasMinkowskiBounds := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hL.posDef_integralNorm (b 0) (b.ne_zero 0)
  · exact hb.monotone_integralNorm (by decide : (0 : Fin 3) ≤ 1)
  · exact hb.monotone_integralNorm (by decide : (1 : Fin 3) ≤ 2)
  · simpa [ofBasis] using hb.two_mul_abs_integralForm_le h01
  · simpa [ofBasis] using hb.two_mul_abs_integralForm_le h02
  · simpa [ofBasis] using hb.two_mul_abs_integralForm_le h12

/-- The Gram matrix of a Minkowski-reduced ternary basis satisfies
`HasSignSumBounds`. These inequalities let the proof of Mahler's bound move
the three off-diagonal coefficients into one sign chamber without changing
their absolute values or their product. -/
theorem hasSignSumBounds_of_isMinkowskiReduced
    (L : IntegralLattice V) (b : Module.Basis (Fin 3) ℤ L)
    (hb : L.IsMinkowskiReduced b) :
    (ofBasis L b).HasSignSumBounds := by
  have hcoord_pp : b.coord 2 (b 0 + b 1) = 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hcoord_pm : b.coord 2 (b 0 - b 1) = 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hcoord_mp : b.coord 2 (-b 0 + b 1) = 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hcoord_mm : b.coord 2 (-b 0 - b 1) = 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hpp := hb.integralNorm_le_integralNorm_add (2 : Fin 3) hcoord_pp
  have hpm := hb.integralNorm_le_integralNorm_add (2 : Fin 3) hcoord_pm
  have hmp := hb.integralNorm_le_integralNorm_add (2 : Fin 3) hcoord_mp
  have hmm := hb.integralNorm_le_integralNorm_add (2 : Fin 3) hcoord_mm
  simp [IntegralLattice.integralNorm_add, IntegralLattice.integralNorm_sub,
    L.isSymm_integralForm.eq] at hpp hpm hmp hmm
  dsimp only [HasSignSumBounds, ofBasis]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The determinant of the matrix of `g` is `g.det`. -/
theorem det_matrix (g : TernaryGram) : g.matrix.det = g.det := by
  simp [TernaryGram.matrix, TernaryGram.det, Matrix.det_fin_three]
  ring

/-- The determinant of the Gram matrix of any basis of `L` is the
determinant of `L`. -/
theorem det_ofBasis (L : IntegralLattice V) (b : Module.Basis (Fin 3) ℤ L) :
    (ofBasis L b).det = L.determinant := by
  rw [← det_matrix, matrix_ofBasis, ← IntegralLattice.gramDet_def,
    ← L.determinant_eq_gramDet b]

export TernaryReductionBounds
  (two_mul_abc_le_four_det_of_sign_sums)

/-- Mahler's bound in doubled form: under `HasMinkowskiBounds` and
`HasSignSumBounds`, `2abc ≤ 4 det`. -/
theorem two_mul_product_le_four_determinant {g : TernaryGram}
    (hsize : g.HasMinkowskiBounds) (hsum : g.HasSignSumBounds) :
    2 * g.a * g.b * g.c ≤ 4 * g.det := by
  rcases hsize with ⟨ha, hab, hbc, hx, hy, hz⟩
  rcases hsum with ⟨h₁, h₂, h₃, h₄⟩
  have h := two_mul_abc_le_four_det_of_sign_sums
    g.a g.b g.c (2 * g.r) (2 * g.s) (2 * g.t) ha hab hbc
    (by simpa [abs_mul] using hx) (by simpa [abs_mul] using hy)
    (by simpa [abs_mul] using hz) h₁ h₂ h₃ h₄
  dsimp [TernaryGram.det]
  nlinarith

/-- Mahler's bound: under `HasMinkowskiBounds` and `HasSignSumBounds`, the
product of the diagonal entries is at most twice the determinant. The finite
classifications at determinants 3, 6, 7, and 10 use this bound. -/
theorem product_le_two_mul_determinant {g : TernaryGram}
    (hsize : g.HasMinkowskiBounds) (hsum : g.HasSignSumBounds) :
    g.a * g.b * g.c ≤ 2 * g.det := by
  nlinarith [two_mul_product_le_four_determinant hsize hsum]

/-- Mahler's bound for the Gram matrix of a Minkowski-reduced basis of a
positive-definite ternary lattice `L`: `abc ≤ 2 det L`. -/
theorem product_le_two_mul_determinant_of_isMinkowskiReduced
    (L : IntegralLattice V) (hL : L.IsPosDef)
    (b : Module.Basis (Fin 3) ℤ L) (hb : L.IsMinkowskiReduced b) :
    (ofBasis L b).a * (ofBasis L b).b * (ofBasis L b).c ≤
      2 * L.determinant := by
  rw [← det_ofBasis L b]
  exact product_le_two_mul_determinant
    (hasMinkowskiBounds_of_isMinkowskiReduced L hL b hb)
    (hasSignSumBounds_of_isMinkowskiReduced L b hb)

/-- The box that contains the Gram matrix of every Minkowski-reduced basis at
determinant `D`: `0 < a ≤ b ≤ c ≤ 2D`, `2|r| ≤ a`, `2|s| ≤ a`, `2|t| ≤ b`,
`abc ≤ 2D`, and `det = D`. The sign-sum inequalities are used only to prove
`abc ≤ 2D` and are not part of the box. -/
def IsBoundedDeterminantCandidate (D : ℤ) (g : TernaryGram) : Prop :=
  0 < g.a ∧ g.a ≤ g.b ∧ g.b ≤ g.c ∧ g.c ≤ 2 * D ∧
    2 * |g.r| ≤ g.a ∧ 2 * |g.s| ≤ g.a ∧ 2 * |g.t| ≤ g.b ∧
    g.a * g.b * g.c ≤ 2 * D ∧ g.det = D

/-- The Gram matrix of a Minkowski-reduced basis of a positive-definite
ternary lattice of determinant `D` lies in the box
`IsBoundedDeterminantCandidate D`. -/
theorem isBoundedDeterminantCandidate_of_isMinkowskiReduced
    (L : IntegralLattice V) (hL : L.IsPosDef)
    (b : Module.Basis (Fin 3) ℤ L) (hb : L.IsMinkowskiReduced b)
    (D : ℤ) (hdet : L.determinant = D) :
    IsBoundedDeterminantCandidate D (ofBasis L b) := by
  have hm := hasMinkowskiBounds_of_isMinkowskiReduced L hL b hb
  have hp := product_le_two_mul_determinant_of_isMinkowskiReduced L hL b hb
  rw [hdet] at hp
  have hc0 : 0 ≤ (ofBasis L b).c := (lt_of_lt_of_le
    (lt_of_lt_of_le hm.1 hm.2.1) hm.2.2.1).le
  have ha_pos : 0 < (ofBasis L b).a := hm.1
  have ha1 : 1 ≤ (ofBasis L b).a := by omega
  have hb1 : 1 ≤ (ofBasis L b).b := le_trans ha1 hm.2.1
  have hab1 : 1 ≤ (ofBasis L b).a * (ofBasis L b).b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)]
  have hcD : (ofBasis L b).c ≤ 2 * D := by
    have hmul := mul_nonneg (sub_nonneg.mpr hab1) hc0
    nlinarith
  refine ⟨hm.1, hm.2.1, hm.2.2.1, hcD, hm.2.2.2.1,
    hm.2.2.2.2.1, hm.2.2.2.2.2, hp, ?_⟩
  exact (det_ofBasis L b).trans hdet

/-- Every positive-definite lattice of rank 3 and determinant `D` has a
basis whose Gram matrix lies in the box `IsBoundedDeterminantCandidate D`. -/
theorem exists_basis_isBoundedDeterminantCandidate
    (L : IntegralLattice V) (hL : L.IsPosDef)
    (hrank : Module.finrank ℤ L = 3) (D : ℤ) (hdet : L.determinant = D) :
    ∃ b : Module.Basis (Fin 3) ℤ L,
      IsBoundedDeterminantCandidate D (ofBasis L b) := by
  have hred : ∃ b : Module.Basis (Fin 3) ℤ L,
      L.IsMinkowskiReduced b :=
    hrank ▸ hL.isPosSemidef.exists_isMinkowskiReduced
  obtain ⟨b, hb⟩ := hred
  exact ⟨b, isBoundedDeterminantCandidate_of_isMinkowskiReduced
    L hL b hb D hdet⟩

/- For determinants at most 10, the box forces `a ≤ 2` and `b ≤ 4`; the
finite searches use these ranges. -/
export TernaryReductionBounds (small_diagonal_ranges)

/-- The norm of `x b₀ + y b₁ + z b₂` is the value of the form `ofBasis L b`
at `(x, y, z)`. -/
theorem integralNorm_linearCombination (L : IntegralLattice V)
    (b : Module.Basis (Fin 3) ℤ L) (x y z : ℤ) :
    L.integralNorm (x • b 0 + y • b 1 + z • b 2) =
      (ofBasis L b).eval x y z := by
  have h10 := L.isSymm_integralForm.eq (b 1) (b 0)
  have h20 := L.isSymm_integralForm.eq (b 2) (b 0)
  have h21 := L.isSymm_integralForm.eq (b 2) (b 1)
  simp only [IntegralLattice.integralNorm_apply, ofBasis,
    TernaryGram.eval, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [h10, h20, h21]
  ring

/-- The norm of a lattice vector is the value of the form `ofBasis L b` at its
coordinates in the basis `b`. -/
theorem integralNorm_eq_eval_repr (L : IntegralLattice V)
    (b : Module.Basis (Fin 3) ℤ L) (v : L) :
    L.integralNorm v = (ofBasis L b).eval
      (b.repr v 0) (b.repr v 1) (b.repr v 2) := by
  have hv : b.repr v 0 • b 0 + b.repr v 1 • b 1 + b.repr v 2 • b 2 = v := by
    simpa only [Fin.sum_univ_three] using b.sum_repr v
  calc
    L.integralNorm v =
        L.integralNorm (b.repr v 0 • b 0 + b.repr v 1 • b 1 + b.repr v 2 • b 2) :=
      congrArg L.integralNorm hv.symm
    _ = _ := integralNorm_linearCombination L b _ _ _

/-- The form `ofBasis L b` represents `n` if and only if `L` has a vector of
norm `n`. -/
theorem represents_ofBasis_iff (L : IntegralLattice V)
    (b : Module.Basis (Fin 3) ℤ L) (n : ℤ) :
    (ofBasis L b).Represents n ↔ ∃ v : L, L.integralNorm v = n := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨x • b 0 + y • b 1 + z • b 2,
      (integralNorm_linearCombination L b x y z).trans h⟩
  · rintro ⟨v, hv⟩
    exact ⟨b.repr v 0, b.repr v 1, b.repr v 2,
      (integralNorm_eq_eval_repr L b v).symm.trans hv⟩

end TernaryGram

end FibonacciCriterion

