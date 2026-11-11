import FibonacciCriterion.ClassicalInputs.Reduction.Lattice
import FibonacciCriterion.ClassicalInputs.DeterminantSeven.ZeroCount
import FibonacciCriterion.ClassicalInputs.Reduction.Bounds
import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates
import TauCeti.LinearAlgebra.IntegralLattice.Norm
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.ReducedGram
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume
import TauCeti.Data.Nat.Prime.IntCast
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Changes of basis and reduction modulo 7

An integral change of basis reduces modulo 7 to a `ModSevenIsometry`
(`modSevenIsometryOfIntMatrices`). Hence the Gram matrices of two bases of
the same lattice have the same number of zeros modulo 7
(`modSevenIsometryOfBases`). The standard basis of `tauLattice A` has Gram
matrix `A` (`ofBasis_canonical`). `ClassicalInputs.DeterminantSeven.GramMatrices`
uses this to carry the zero count from a constructed Gram matrix to a
Minkowski-reduced one.
-/

namespace FibonacciCriterion.DeterminantSevenGenus

open TauCeti

/-- If `P` and `Q` are mutually inverse integral matrices and
`B = Pᵀ A P`, then `v ↦ P v` modulo 7 is a `ModSevenIsometry A B`. -/
noncomputable def modSevenIsometryOfIntMatrices (A B : TernaryGram)
    (P Q : Matrix (Fin 3) (Fin 3) ℤ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hGram : B.matrix = P.transpose * A.matrix * P) :
    ModSevenIsometry A B := by
  let f : ℤ →+* ZMod 7 := Int.castRingHom (ZMod 7)
  let p : Matrix (Fin 3) (Fin 3) (ZMod 7) := f.mapMatrix P
  let q : Matrix (Fin 3) (Fin 3) (ZMod 7) := f.mapMatrix Q
  have hpq : p * q = 1 := by
    simp only [p, q, ← map_mul, hPQ, map_one]
  have hqp : q * p = 1 := by
    simp only [p, q, ← map_mul, hQP, map_one]
  have hred : f.mapMatrix B.matrix = p.transpose * f.mapMatrix A.matrix * p := by
    simp only [p, hGram, map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map]
  refine ⟨{
    toFun := fun v => Matrix.mulVec p v
    invFun := fun v => Matrix.mulVec q v
    left_inv := ?_
    right_inv := ?_ }, ?_⟩
  · intro v
    change Matrix.mulVec q (Matrix.mulVec p v) = v
    rw [Matrix.mulVec_mulVec, hqp, Matrix.one_mulVec]
  · intro v
    change Matrix.mulVec p (Matrix.mulVec q v) = v
    rw [Matrix.mulVec_mulVec, hpq, Matrix.one_mulVec]
  · intro v
    have h := congrArg (fun G : Matrix (Fin 3) (Fin 3) (ZMod 7) =>
      dotProduct v (Matrix.mulVec G v)) hred
    simp [f, TernaryGram.evalModSeven, TernaryGram.matrix,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ] at h ⊢
    linear_combination -h

/-- The Gram matrices of two bases of the same lattice are related by the
integral change-of-basis matrix, so their reductions modulo 7 are related
by a `ModSevenIsometry`. -/
noncomputable def modSevenIsometryOfBases (L : IntegralLattice (Fin 3 → ℚ))
    (b c : Module.Basis (Fin 3) ℤ L) :
    ModSevenIsometry (TernaryGram.ofBasis L b) (TernaryGram.ofBasis L c) :=
  modSevenIsometryOfIntMatrices _ _ (b.toMatrix c) (c.toMatrix b)
    (b.toMatrix_mul_toMatrix_flip c) (c.toMatrix_mul_toMatrix_flip b) (by
      rw [TernaryGram.matrix_ofBasis, TernaryGram.matrix_ofBasis, L.gramMatrix_eq_toMatrix,
        L.gramMatrix_eq_toMatrix, LinearMap.BilinForm.toMatrix_mul_basis_toMatrix])

/-- The Gram matrix of the standard basis of `tauLattice A` is `A`. -/
theorem ofBasis_canonical (A : TernaryGram) :
    TernaryGram.ofBasis (tauLattice A)
      (IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin 3))
        A.matrix A.matrix_isSymm) = A := by
  have h := TernaryGram.matrix_ofBasis (tauLattice A)
    (IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin 3))
      A.matrix A.matrix_isSymm)
  have hcanonical :=
    IntegralLattice.gramMatrix_ofGramMatrix (Pi.basisFun ℚ (Fin 3))
      A.matrix A.matrix_isSymm
  have h' : (TernaryGram.ofBasis (tauLattice A)
      (IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin 3))
        A.matrix A.matrix_isSymm)).matrix = A.matrix :=
    h.trans (by simpa only [tauLattice] using hcanonical)

  have ha := congrArg (fun G => G 0 0) h'
  have hb := congrArg (fun G => G 1 1) h'
  have hc := congrArg (fun G => G 2 2) h'
  have hr := congrArg (fun G => G 0 1) h'
  have hs := congrArg (fun G => G 0 2) h'
  have ht := congrArg (fun G => G 1 2) h'
  simp [TernaryGram.matrix] at ha hb hc hr hs ht
  let G := TernaryGram.ofBasis (tauLattice A)
    (IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin 3))
      A.matrix A.matrix_isSymm)
  change G = A
  change G.a = A.a at ha
  change G.b = A.b at hb
  change G.c = A.c at hc
  change G.r = A.r at hr
  change G.s = A.s at hs
  change G.t = A.t at ht
  cases hG : G
  cases hA : A
  simp only [hG, hA] at ha hb hc hr hs ht ⊢
  congr

end FibonacciCriterion.DeterminantSevenGenus
