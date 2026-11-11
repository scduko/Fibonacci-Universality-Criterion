import FibonacciCriterion.Forms.TernaryGram

/-!
# The forms `f` and `h` and square transfers

The ternary forms `f = x² + 2y² + 2yz + 4z²` and `h = ⟨1,1,7⟩` of determinant
7, with the integral Gram-matrix convention of the manuscript, their Gram
matrices (`fGram`, `hGram`), and the square transfers of identity (8),
`Bᵀ G_f B = p² G_h` (`IsSquareTransfer`). This file proves only the algebraic
transfer of representations; the
representation of eligible integers by `f` or `h` (Proposition 3.3) is
`DeterminantSevenGenus.eligible_f_or_h`.
-/

namespace FibonacciCriterion.Irregular

/-- The irregular ternary form `f`, with Gram matrix
`[[1,0,0],[0,2,1],[0,1,4]]`. -/
def f (x y z : ℤ) : ℤ := x ^ 2 + 2 * y ^ 2 + 2 * y * z + 4 * z ^ 2

/-- The diagonal form `h = ⟨1,1,7⟩`, the other form of determinant 7 in
Proposition 3.3. -/
def h (x y z : ℤ) : ℤ := x ^ 2 + y ^ 2 + 7 * z ^ 2

/-- Representation of `n` by `f`. -/
def RepresentsF (n : ℤ) : Prop := ∃ x y z : ℤ, f x y z = n

/-- Representation of `n` by `h`. -/
def RepresentsH (n : ℤ) : Prop := ∃ x y z : ℤ, h x y z = n

/-- The Gram matrix of `f`. -/
abbrev fGram : TernaryGram := ⟨1, 2, 4, 0, 0, 1⟩

/-- The Gram matrix `diag(1, 1, 7)` of `h`. -/
def hGram : TernaryGram := ⟨1, 1, 7, 0, 0, 0⟩

/-- The form of `fGram` is `f`. -/
theorem fGram_eval (x y z : ℤ) : fGram.eval x y z = f x y z := by
  simp only [TernaryGram.eval, f]
  ring

/-- The form of `hGram` is `h`. -/
theorem hGram_eval (x y z : ℤ) : hGram.eval x y z = h x y z := by
  simp [hGram, TernaryGram.eval, h]

/-- `fGram` represents `n` exactly when `f` does. -/
theorem fGram_represents_iff (n : ℤ) : fGram.Represents n ↔ RepresentsF n := by
  simp only [TernaryGram.Represents, RepresentsF, fGram_eval]

/-- `hGram` represents `n` exactly when `h` does. -/
theorem hGram_represents_iff (n : ℤ) : hGram.Represents n ↔ RepresentsH n := by
  simp only [TernaryGram.Represents, RepresentsH, hGram_eval]

/-- An integral linear map of `ℤ³`, stored by the entries of its matrix. -/
structure TernaryLinearMap where
  /-- The entry in row 1 and column 1 of the matrix. -/
  a11 : ℤ
  /-- The entry in row 1 and column 2 of the matrix. -/
  a12 : ℤ
  /-- The entry in row 1 and column 3 of the matrix. -/
  a13 : ℤ
  /-- The entry in row 2 and column 1 of the matrix. -/
  a21 : ℤ
  /-- The entry in row 2 and column 2 of the matrix. -/
  a22 : ℤ
  /-- The entry in row 2 and column 3 of the matrix. -/
  a23 : ℤ
  /-- The entry in row 3 and column 1 of the matrix. -/
  a31 : ℤ
  /-- The entry in row 3 and column 2 of the matrix. -/
  a32 : ℤ
  /-- The entry in row 3 and column 3 of the matrix. -/
  a33 : ℤ

namespace TernaryLinearMap

/-- The first coordinate of the image of `(u, v, w)` under `B`. -/
def x (B : TernaryLinearMap) (u v w : ℤ) : ℤ := B.a11 * u + B.a12 * v + B.a13 * w
/-- The second coordinate of the image of `(u, v, w)` under `B`. -/
def y (B : TernaryLinearMap) (u v w : ℤ) : ℤ := B.a21 * u + B.a22 * v + B.a23 * w
/-- The third coordinate of the image of `(u, v, w)` under `B`. -/
def z (B : TernaryLinearMap) (u v w : ℤ) : ℤ := B.a31 * u + B.a32 * v + B.a33 * w

end TernaryLinearMap

/-- Identity (8), `Bᵀ G_f B = p² G_h`, in polynomial form: `f(Bv) = p² h(v)`
for every integral vector `v`. -/
def IsSquareTransfer (p : ℤ) (B : TernaryLinearMap) : Prop :=
  ∀ x y z : ℤ, f (B.x x y z) (B.y x y z) (B.z x y z) = p ^ 2 * h x y z

/-- Scaling a vector by `a` multiplies the value of `f` by `a²`. -/
theorem f_scale (a x y z : ℤ) :
    f (a * x) (a * y) (a * z) = a ^ 2 * f x y z := by
  unfold f
  ring

/-- If `f` represents `n`, then it represents `a² n`. -/
theorem representsF_square_mul {n : ℤ} (hn : RepresentsF n) (a : ℤ) :
    RepresentsF (a ^ 2 * n) := by
  rcases hn with ⟨x, y, z, hxyz⟩
  refine ⟨a * x, a * y, a * z, ?_⟩
  rw [f_scale, hxyz]

/-- If `B` satisfies identity (8) and `h` represents `n`, then `f` represents
`p² n`. -/
theorem representsF_of_squareTransfer {p n : ℤ} {B : TernaryLinearMap}
    (hB : IsSquareTransfer p B) (hn : RepresentsH n) :
    RepresentsF (p ^ 2 * n) := by
  rcases hn with ⟨x, y, z, hxyz⟩
  refine ⟨B.x x y z, B.y x y z, B.z x y z, ?_⟩
  rw [hB x y z, hxyz]

/-- If `B` satisfies identity (8) and `n` is represented by `f` or `h`, then
`f` represents `p² n`. Proposition 3.3 supplies the hypothesis for eligible
`n`. -/
theorem representsF_of_either_class {p n : ℤ} {B : TernaryLinearMap}
    (hB : IsSquareTransfer p B) (hn : RepresentsF n ∨ RepresentsH n) :
    RepresentsF (p ^ 2 * n) := by
  rcases hn with hf | hh
  · exact representsF_square_mul hf p
  · exact representsF_of_squareTransfer hB hh

end FibonacciCriterion.Irregular
