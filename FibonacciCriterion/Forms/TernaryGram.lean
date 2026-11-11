import Mathlib

/-!
# Symmetric ternary Gram matrices

`TernaryGram` stores a symmetric integral 3 × 3 matrix by its six
coefficients, and `Change` stores an integral change of variables. This file
defines the determinant, the quadratic and bilinear forms, the pullback
`Bᵀ A B`, and representation of integers. The nine ternary escalators
(`escalatorGram`), their quaternary extensions (`QuaternaryExtension`), and the
finite classifications at determinants 3, 6, 7, and 10 use this format.
-/

namespace FibonacciCriterion

/-- A symmetric integral 3 × 3 matrix `[[a,r,s],[r,b,t],[s,t,c]]`, stored by
its diagonal and upper-triangular entries. -/
structure TernaryGram where
  /-- The first diagonal entry, the coefficient of `x²`. -/
  a : ℤ
  /-- The second diagonal entry, the coefficient of `y²`. -/
  b : ℤ
  /-- The third diagonal entry, the coefficient of `z²`. -/
  c : ℤ
  /-- The entry at `(1,2)` and `(2,1)`; the coefficient of `xy` is `2r`. -/
  r : ℤ
  /-- The entry at `(1,3)` and `(3,1)`; the coefficient of `xz` is `2s`. -/
  s : ℤ
  /-- The entry at `(2,3)` and `(3,2)`; the coefficient of `yz` is `2t`. -/
  t : ℤ
deriving DecidableEq

namespace TernaryGram

/-- The determinant of the matrix. -/
def det (A : TernaryGram) : ℤ :=
  A.a * A.b * A.c + 2 * A.r * A.s * A.t -
    A.a * A.t ^ 2 - A.b * A.s ^ 2 - A.c * A.r ^ 2

/-- The quadratic form `ax² + by² + cz² + 2rxy + 2sxz + 2tyz` of the matrix. -/
def eval (A : TernaryGram) (x y z : ℤ) : ℤ :=
  A.a * x ^ 2 + A.b * y ^ 2 + A.c * z ^ 2 +
    2 * A.r * x * y + 2 * A.s * x * z + 2 * A.t * y * z

/-- The symmetric bilinear form of the matrix. -/
def bil (A : TernaryGram) (x₁ x₂ x₃ y₁ y₂ y₃ : ℤ) : ℤ :=
  A.a * x₁ * y₁ + A.b * x₂ * y₂ + A.c * x₃ * y₃ +
    A.r * (x₁ * y₂ + x₂ * y₁) +
    A.s * (x₁ * y₃ + x₃ * y₁) +
    A.t * (x₂ * y₃ + x₃ * y₂)

end TernaryGram

/-- An integral 3 × 3 matrix, used as a change of variables and stored by
rows. -/
structure Change where
  /-- The entry in row 1 and column 1. -/
  m11 : ℤ
  /-- The entry in row 1 and column 2. -/
  m12 : ℤ
  /-- The entry in row 1 and column 3. -/
  m13 : ℤ
  /-- The entry in row 2 and column 1. -/
  m21 : ℤ
  /-- The entry in row 2 and column 2. -/
  m22 : ℤ
  /-- The entry in row 2 and column 3. -/
  m23 : ℤ
  /-- The entry in row 3 and column 1. -/
  m31 : ℤ
  /-- The entry in row 3 and column 2. -/
  m32 : ℤ
  /-- The entry in row 3 and column 3. -/
  m33 : ℤ
deriving DecidableEq

namespace Change

/-- The determinant of the matrix. -/
def det (B : Change) : ℤ :=
  B.m11 * (B.m22 * B.m33 - B.m23 * B.m32) -
    B.m12 * (B.m21 * B.m33 - B.m23 * B.m31) +
    B.m13 * (B.m21 * B.m32 - B.m22 * B.m31)

/-- The adjugate matrix. For `B` of determinant `±1` it is `±B⁻¹`. -/
def adjugate (B : Change) : Change where
  m11 := B.m22 * B.m33 - B.m23 * B.m32
  m12 := B.m13 * B.m32 - B.m12 * B.m33
  m13 := B.m12 * B.m23 - B.m13 * B.m22
  m21 := B.m23 * B.m31 - B.m21 * B.m33
  m22 := B.m11 * B.m33 - B.m13 * B.m31
  m23 := B.m13 * B.m21 - B.m11 * B.m23
  m31 := B.m21 * B.m32 - B.m22 * B.m31
  m32 := B.m12 * B.m31 - B.m11 * B.m32
  m33 := B.m11 * B.m22 - B.m12 * B.m21

/-- The pullback `Bᵀ A B`, stored by its six coefficients. -/
def pullback (B : Change) (A : TernaryGram) : TernaryGram where
  a := A.bil B.m11 B.m21 B.m31 B.m11 B.m21 B.m31
  b := A.bil B.m12 B.m22 B.m32 B.m12 B.m22 B.m32
  c := A.bil B.m13 B.m23 B.m33 B.m13 B.m23 B.m33
  r := A.bil B.m11 B.m21 B.m31 B.m12 B.m22 B.m32
  s := A.bil B.m11 B.m21 B.m31 B.m13 B.m23 B.m33
  t := A.bil B.m12 B.m22 B.m32 B.m13 B.m23 B.m33

end Change

/-- Representation of `n` by the form of `A`: some integral `(x, y, z)` has
`A.eval x y z = n`. -/
def TernaryGram.Represents (A : TernaryGram) (n : ℤ) : Prop :=
  ∃ x y z : ℤ, A.eval x y z = n

theorem Change.pullback_eval (B : Change) (A : TernaryGram) (x y z : ℤ) :
    (B.pullback A).eval x y z =
      A.eval (B.m11 * x + B.m12 * y + B.m13 * z)
        (B.m21 * x + B.m22 * y + B.m23 * z)
        (B.m31 * x + B.m32 * y + B.m33 * z) := by
  simp only [Change.pullback, TernaryGram.eval, TernaryGram.bil]
  ring

/-- An integer represented by `Bᵀ A B` is represented by `A`, for every
integral `B`, invertible or not. -/
theorem Change.represents_of_pullback (B : Change) (A : TernaryGram)
    {n : ℤ} (hn : (B.pullback A).Represents n) : A.Represents n := by
  rcases hn with ⟨x, y, z, hxyz⟩
  refine ⟨B.m11 * x + B.m12 * y + B.m13 * z,
    B.m21 * x + B.m22 * y + B.m23 * z,
    B.m31 * x + B.m32 * y + B.m33 * z, ?_⟩
  exact (B.pullback_eval A x y z).symm.trans hxyz

/-- The symmetric matrix stored by a `TernaryGram`. -/
def TernaryGram.matrix (A : TernaryGram) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![A.a, A.r, A.s; A.r, A.b, A.t; A.s, A.t, A.c]

theorem TernaryGram.matrix_isSymm (A : TernaryGram) : A.matrix.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end FibonacciCriterion
