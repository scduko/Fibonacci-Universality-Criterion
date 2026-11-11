import FibonacciCriterion.Forms.TernaryGram
import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates
import TauCeti.LinearAlgebra.IntegralLattice.Norm
import TauCeti.LinearAlgebra.IntegralLattice.Gram
import TauCeti.LinearAlgebra.IntegralLattice.Signature

/-!
# Ternary Gram matrices as TauCeti lattices

`tauLattice A` is the TauCeti integral lattice on `ℚ³` whose Gram matrix in the
standard basis is `A`. It represents the same integers as `A`
(`represents_iff_exists_integralNorm`), has rank 3 and determinant `A.det`,
and is positive definite when the form of `A` is positive on nonzero integral
vectors. Conversely, `TernaryGram.ofBasis` reads the Gram matrix of a basis of
a TauCeti lattice. `ClassicalInputs.Reduction.ReducedGram` and
`ClassicalInputs.Reduction.Classification` use this to apply TauCeti's
Minkowski reduction to a `TernaryGram`.
-/

namespace FibonacciCriterion

open TauCeti
open Module

/-- The TauCeti integral lattice on `ℚ³` whose Gram matrix in the standard
basis is `A`. -/
noncomputable def tauLattice (A : TernaryGram) :
    IntegralLattice (Fin 3 → ℚ) :=
  IntegralLattice.ofGramMatrix (Pi.basisFun ℚ (Fin 3)) A.matrix A.matrix_isSymm

/-- The vector of `tauLattice A` with integral coordinates `(x, y, z)`. -/
noncomputable def tauVector (A : TernaryGram) (x y z : ℤ) : tauLattice A := by
  let v : Fin 3 → ℚ := ![(x : ℚ), (y : ℚ), (z : ℚ)]
  refine ⟨v, ?_⟩
  change v ∈
    (IntegralLattice.ofGramMatrix (Pi.basisFun ℚ (Fin 3))
      A.matrix A.matrix_isSymm).carrier
  rw [IntegralLattice.mem_ofGramMatrix_basisFun_carrier_iff]
  intro i
  fin_cases i
  · exact ⟨x, rfl⟩
  · exact ⟨y, rfl⟩
  · exact ⟨z, rfl⟩

@[simp] theorem tauVector_coe (A : TernaryGram) (x y z : ℤ) :
    (tauVector A x y z : Fin 3 → ℚ) =
      ![(x : ℚ), (y : ℚ), (z : ℚ)] := by
  rfl

/-- The norm of the vector with coordinates `(x, y, z)` is `A.eval x y z`. -/
theorem tauVector_integralNorm (A : TernaryGram) (x y z : ℤ) :
    (tauLattice A).integralNorm (tauVector A x y z) = A.eval x y z := by
  apply Int.cast_injective (α := ℚ)
  rw [IntegralLattice.integralNorm_cast, IntegralLattice.norm_apply,
    tauVector_coe, tauLattice,
    IntegralLattice.form_ofGramMatrix_basisFun_apply]
  simp [TernaryGram.matrix, TernaryGram.eval, Fin.sum_univ_succ]
  ring

/-- `A` represents `n` if and only if `tauLattice A` has a vector of
norm `n`. -/
theorem represents_iff_exists_integralNorm (A : TernaryGram) (n : ℤ) :
    A.Represents n ↔
      ∃ v : tauLattice A, (tauLattice A).integralNorm v = n := by
  constructor
  · rintro ⟨x, y, z, hxyz⟩
    exact ⟨tauVector A x y z, (tauVector_integralNorm A x y z).trans hxyz⟩
  · rintro ⟨v, hv⟩
    have hcoords :=
      (IntegralLattice.mem_ofGramMatrix_basisFun_carrier_iff
        A.matrix A.matrix_isSymm (v : Fin 3 → ℚ)).mp v.property
    obtain ⟨x, hx⟩ := hcoords 0
    obtain ⟨y, hy⟩ := hcoords 1
    obtain ⟨z, hz⟩ := hcoords 2
    have hvec : (v : Fin 3 → ℚ) = ![(x : ℚ), (y : ℚ), (z : ℚ)] := by
      funext i
      fin_cases i
      · exact hx.symm
      · exact hy.symm
      · exact hz.symm
    refine ⟨x, y, z, ?_⟩
    have hnorm := tauVector_integralNorm A x y z
    have hv' : v = tauVector A x y z := by
      apply Subtype.ext
      simpa only [tauVector_coe] using hvec
    rw [← hnorm, ← hv', hv]

/-! ## Rank, determinant, and positive definiteness -/

/-- `tauLattice A` has rank 3. -/
theorem tauLattice_finrank (A : TernaryGram) :
    Module.finrank ℤ (tauLattice A) = 3 := by
  rw [IntegralLattice.finrank_carrier]
  simp

/-- The determinant of `tauLattice A` is `A.det`. -/
theorem tauLattice_determinant (A : TernaryGram) :
    (tauLattice A).determinant = A.det := by
  rw [tauLattice, IntegralLattice.determinant_ofGramMatrix]
  simp [TernaryGram.matrix, TernaryGram.det, Matrix.det_fin_three]
  ring

/-- If the form of `A` is positive on nonzero integral vectors, then
`tauLattice A` is positive definite on `ℚ³`. The proof clears the three
denominators of a rational vector. -/
theorem tauLattice_isPosDef (A : TernaryGram)
    (hpos : ∀ x y z : ℤ, x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 → 0 < A.eval x y z) :
    (tauLattice A).IsPosDef := by
  apply (tauLattice A).isPosDef_iff.mpr
  intro v hv
  let D : ℤ := (v 0).den * (v 1).den * (v 2).den
  let x : ℤ := (v 0).num * (v 1).den * (v 2).den
  let y : ℤ := (v 1).num * (v 0).den * (v 2).den
  let z : ℤ := (v 2).num * (v 0).den * (v 1).den
  have hn (i : Fin 3) : ((v i).num : ℚ) = v i * ((v i).den : ℚ) :=
    (div_eq_iff (by exact_mod_cast (v i).den_nz)).mp (v i).num_div_den
  have hD : (D : ℚ) ≠ 0 := by
    dsimp [D]
    push_cast
    exact mul_ne_zero
      (mul_ne_zero (by exact_mod_cast (v 0).den_nz)
        (by exact_mod_cast (v 1).den_nz))
      (by exact_mod_cast (v 2).den_nz)
  have hx : (x : ℚ) = D * v 0 := by
    dsimp [x, D]
    push_cast
    rw [hn 0]
    ring
  have hy : (y : ℚ) = D * v 1 := by
    dsimp [y, D]
    push_cast
    rw [hn 1]
    ring
  have hz : (z : ℚ) = D * v 2 := by
    dsimp [z, D]
    push_cast
    rw [hn 2]
    ring
  have hxyz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
    by_contra! h
    apply hv
    funext i
    fin_cases i
    · have h0 : (D : ℚ) * v 0 = 0 := by rw [← hx, h.1]; norm_num
      exact (mul_eq_zero.mp h0).resolve_left hD
    · have h0 : (D : ℚ) * v 1 = 0 := by rw [← hy, h.2.1]; norm_num
      exact (mul_eq_zero.mp h0).resolve_left hD
    · have h0 : (D : ℚ) * v 2 = 0 := by rw [← hz, h.2.2]; norm_num
      exact (mul_eq_zero.mp h0).resolve_left hD
  have hvec : (tauVector A x y z : Fin 3 → ℚ) = (D : ℚ) • v := by
    funext i
    fin_cases i
    · simpa [tauVector_coe] using hx
    · simpa [tauVector_coe] using hy
    · simpa [tauVector_coe] using hz
  have hnorm : 0 < (tauLattice A).norm (tauVector A x y z) := by
    rw [← IntegralLattice.integralNorm_cast, tauVector_integralNorm]
    exact_mod_cast hpos x y z hxyz
  rw [hvec, IntegralLattice.norm_smul] at hnorm
  rw [← IntegralLattice.norm_apply]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hD)).mp hnorm

/-! ## The Gram matrix of a lattice basis -/

/-- The Gram matrix of a basis of a ternary lattice, as a `TernaryGram`. -/
noncomputable def TernaryGram.ofBasis {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : IntegralLattice V) (b : Basis (Fin 3) ℤ L) : TernaryGram where
  a := L.integralNorm (b 0)
  b := L.integralNorm (b 1)
  c := L.integralNorm (b 2)
  r := L.integralForm (b 0) (b 1)
  s := L.integralForm (b 0) (b 2)
  t := L.integralForm (b 1) (b 2)

/-- The matrix of `TernaryGram.ofBasis L b` is the TauCeti Gram matrix
of `b`. -/
theorem TernaryGram.matrix_ofBasis {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : IntegralLattice V) (b : Basis (Fin 3) ℤ L) :
    (TernaryGram.ofBasis L b).matrix = L.gramMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TernaryGram.ofBasis, TernaryGram.matrix, IntegralLattice.integralNorm_apply]
  all_goals exact L.isSymm_integralForm.eq _ _

end FibonacciCriterion
