import Mathlib

/-!
# Positive-definite forms with integral Gram matrices

A `Form ι` is a positive-definite quadratic form on `ℤ^ι` given by an integral
symmetric Gram matrix, so its cross terms have even coefficients. Positive
definiteness is required of the associated real form. The index type `ι` can
be any finite type, including the empty type, so the rank is arbitrary.

The file also defines representation (`Form.Represents`), orthogonal sums
(`Form.orthogonalSum`), diagonal forms (`Form.diagonal`),
Fibonacci-universality (`FibonacciUniversal`), and the forcing property of a
criterion set (`IsFibonacciCriterion`). `Form.posDef_gram` and `Form.ofPosDef`
relate `Form` to Mathlib's `Matrix.PosDef`.

The directory `Forms/` holds the ternary Gram matrices and quaternary
extensions of §4; it does not depend on this file.
-/

namespace FibonacciCriterion

open scoped BigOperators Matrix

variable {ι κ R : Type*} [Fintype ι] [Fintype κ]

/-- The value `xᵀ G x` of the quadratic form with Gram matrix `G`. -/
def gramEval [CommRing R] (G : Matrix ι ι R) (x : ι → R) : R :=
  ∑ i, ∑ j, x i * G i j * x j

@[simp] theorem gramEval_zero [CommRing R] (G : Matrix ι ι R) :
    gramEval G 0 = 0 := by
  simp [gramEval]

/-- A positive-definite quadratic form on `ℤ^ι` with an integral symmetric Gram
matrix. Positive definiteness is required of the associated real form. -/
structure Form (ι : Type*) [Fintype ι] where
  /-- The Gram matrix `G`, with integer entries. -/
  gram : Matrix ι ι ℤ
  /-- The Gram matrix is symmetric. -/
  symmetric : ∀ i j, gram i j = gram j i
  /-- The real quadratic form `x ↦ xᵀ G x` is positive at every nonzero
  vector. -/
  positive : ∀ x : ι → ℝ, x ≠ 0 →
    0 < gramEval (Matrix.of fun i j => (gram i j : ℝ)) x

namespace Form

/-- The value `P(x) = xᵀ G x` of the form at an integer vector `x`. -/
def eval (P : Form ι) (x : ι → ℤ) : ℤ := gramEval P.gram x

/-- `P` represents `n`: some integer vector `x` has `P(x) = n`. -/
def Represents (P : Form ι) (n : ℕ) : Prop :=
  ∃ x : ι → ℤ, P.eval x = (n : ℤ)

@[simp] theorem eval_zero (P : Form ι) : P.eval 0 = 0 := by
  simp [eval]

theorem eval_pos (P : Form ι) (x : ι → ℤ) (hx : x ≠ 0) :
    0 < P.eval x := by
  have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
    intro h
    apply hx
    funext i
    have hi := congrFun h i
    change (x i : ℝ) = 0 at hi
    change x i = 0
    exact_mod_cast hi
  have h := P.positive (fun i => (x i : ℝ)) hx'
  have hcast : (P.eval x : ℝ) =
      gramEval (Matrix.of fun i j => (P.gram i j : ℝ)) (fun i => (x i : ℝ)) := by
    simp [eval, gramEval]
  rw [← hcast] at h
  exact_mod_cast h

theorem eval_nonneg (P : Form ι) (x : ι → ℤ) : 0 ≤ P.eval x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (P.eval_pos x hx).le

/-- The Gram matrix of an orthogonal sum, indexed by the sum type `ι ⊕ κ`. -/
def orthogonalGram [Zero R] (A : Matrix ι ι R) (B : Matrix κ κ R) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) R
  | .inl i, .inl j => A i j
  | .inr i, .inr j => B i j
  | _, _ => 0

theorem gramEval_orthogonalGram [CommRing R]
    (A : Matrix ι ι R) (B : Matrix κ κ R) (x : ι ⊕ κ → R) :
    gramEval (orthogonalGram A B) x =
      gramEval A (fun i => x (.inl i)) + gramEval B (fun j => x (.inr j)) := by
  simp [gramEval, orthogonalGram, Fintype.sum_sum_type]

/-- The orthogonal sum `P ⊥ Q`, a form on `ℤ^(ι ⊕ κ)`. -/
def orthogonalSum (P : Form ι) (Q : Form κ) : Form (ι ⊕ κ) where
  gram := orthogonalGram P.gram Q.gram
  symmetric := by
    intro i j
    cases i <;> cases j <;>
      simp [orthogonalGram, P.symmetric, Q.symmetric]
  positive := by
    intro x hx
    have he :
        gramEval (Matrix.of fun i j => ((orthogonalGram P.gram Q.gram i j : ℤ) : ℝ)) x =
          gramEval (Matrix.of fun i j => (P.gram i j : ℝ)) (fun i => x (.inl i)) +
          gramEval (Matrix.of fun i j => (Q.gram i j : ℝ)) (fun j => x (.inr j)) := by
      simp [gramEval, orthogonalGram, Fintype.sum_sum_type]
    rw [he]
    by_cases hl : (fun i => x (.inl i)) = 0
    · have hr : (fun j => x (.inr j)) ≠ 0 := by
        intro hr
        apply hx
        funext i
        cases i with
        | inl i => exact congrFun hl i
        | inr j => exact congrFun hr j
      rw [hl, gramEval_zero, zero_add]
      exact Q.positive (fun j => x (.inr j)) hr
    · have hp := P.positive (fun i => x (.inl i)) hl
      by_cases hr : (fun j => x (.inr j)) = 0
      · rw [hr, gramEval_zero, add_zero]
        exact hp
      · exact add_pos hp (Q.positive (fun j => x (.inr j)) hr)

@[simp] theorem eval_orthogonalSum (P : Form ι) (Q : Form κ)
    (x : ι ⊕ κ → ℤ) :
    (P.orthogonalSum Q).eval x =
      P.eval (fun i => x (.inl i)) + Q.eval (fun j => x (.inr j)) :=
  gramEval_orthogonalGram P.gram Q.gram x

theorem represents_orthogonalSum_left (P : Form ι) (Q : Form κ) {n : ℕ}
    (h : P.Represents n) : (P.orthogonalSum Q).Represents n := by
  obtain ⟨x, hx⟩ := h
  refine ⟨Sum.elim x 0, ?_⟩
  rw [eval_orthogonalSum]
  change P.eval x + Q.eval (0 : κ → ℤ) = (n : ℤ)
  simpa using hx

theorem represents_orthogonalSum_right (P : Form ι) (Q : Form κ) {n : ℕ}
    (h : Q.Represents n) : (P.orthogonalSum Q).Represents n := by
  obtain ⟨x, hx⟩ := h
  refine ⟨Sum.elim 0 x, ?_⟩
  rw [eval_orthogonalSum]
  change P.eval (0 : ι → ℤ) + Q.eval x = (n : ℤ)
  simpa using hx

section Diagonal

variable [DecidableEq ι]

theorem gramEval_diagonal [CommRing R] (w : ι → R) (x : ι → R) :
    gramEval (Matrix.diagonal w) x = ∑ i, w i * x i ^ 2 := by
  classical
  simp [gramEval, Matrix.diagonal, mul_ite, pow_two,
    mul_comm, mul_left_comm]

/-- The diagonal form `∑ i, w i * x i ^ 2` with positive coefficients `w`. -/
def diagonal (w : ι → ℤ) (hw : ∀ i, 0 < w i) : Form ι where
  gram := Matrix.diagonal w
  symmetric := by
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp [Matrix.diagonal, h, Ne.symm h]
  positive := by
    intro x hx
    have he :
        gramEval (Matrix.of fun i j => (((Matrix.diagonal w) i j : ℤ) : ℝ)) x =
          ∑ i, (w i : ℝ) * x i ^ 2 := by
      simp [gramEval, Matrix.diagonal, mul_ite, pow_two,
        mul_comm, mul_left_comm, mul_assoc]
    rw [he]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      exact h i
    have hwi : (0 : ℝ) < w i := by exact_mod_cast hw i
    have hp : 0 < (w i : ℝ) * x i ^ 2 := mul_pos hwi (sq_pos_of_ne_zero hi)
    have hnonneg (j : ι) : 0 ≤ (w j : ℝ) * x j ^ 2 := by
      apply mul_nonneg
      · exact_mod_cast (hw j).le
      · exact sq_nonneg (x j)
    exact hp.trans_le (Finset.single_le_sum
      (fun j _ => hnonneg j)
      (Finset.mem_univ i))

@[simp] theorem eval_diagonal (w : ι → ℤ) (hw : ∀ i, 0 < w i) (x : ι → ℤ) :
    (diagonal w hw).eval x = ∑ i, w i * x i ^ 2 :=
  gramEval_diagonal w x

/-- If every diagonal coefficient is at least `b`, the diagonal form takes
values at least `b` at nonzero vectors. -/
theorem diagonal_lower_bound (w : ι → ℤ) (hw : ∀ i, 0 < w i)
    (b : ℤ) (hb : ∀ i, b ≤ w i) (x : ι → ℤ) (hx : x ≠ 0) :
    b ≤ (diagonal w hw).eval x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  have hs : 1 ≤ x i ^ 2 := by
    have hp := sq_pos_of_ne_zero hi
    omega
  rw [eval_diagonal]
  calc
    b ≤ w i := hb i
    _ ≤ w i * x i ^ 2 := by
      simpa using (mul_le_mul_of_nonneg_left hs (hw i).le)
    _ ≤ ∑ j, w j * x j ^ 2 := Finset.single_le_sum
      (fun j _ => mul_nonneg (hw j).le (sq_nonneg (x j))) (Finset.mem_univ i)

end Diagonal

/-! ### Comparison with Mathlib

A `Form` is the same thing as an integer matrix whose real form is positive
definite in the sense of `Matrix.PosDef`, and `P.eval x` is `x ⬝ᵥ G *ᵥ x`. -/

/-- `gramEval G x` is `x ⬝ᵥ G *ᵥ x`. -/
theorem _root_.FibonacciCriterion.gramEval_eq_dotProduct [CommRing R]
    (G : Matrix ι ι R) (x : ι → R) : gramEval G x = x ⬝ᵥ G *ᵥ x := by
  simp [gramEval, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- The value of a form is `x ⬝ᵥ G *ᵥ x`, with `G` its Gram matrix. -/
theorem eval_eq_dotProduct (P : Form ι) (x : ι → ℤ) :
    P.eval x = x ⬝ᵥ P.gram *ᵥ x :=
  gramEval_eq_dotProduct P.gram x

/-- The Gram matrix of a form, with real entries, is positive definite in
Mathlib's sense. -/
theorem posDef_gram (P : Form ι) : (P.gram.map (Int.cast : ℤ → ℝ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, P.symmetric j i]
  · have h := P.positive x hx
    rw [gramEval_eq_dotProduct] at h
    rw [star_trivial]
    exact h

/-- The form with Gram matrix `G`, for an integer matrix `G` that is positive
definite over `ℝ` in Mathlib's sense. -/
def ofPosDef (G : Matrix ι ι ℤ) (hG : (G.map (Int.cast : ℤ → ℝ)).PosDef) :
    Form ι where
  gram := G
  symmetric := fun i j => by
    have h := congrFun (congrFun hG.isHermitian j) i
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial] at h
    exact_mod_cast h
  positive := fun x hx => by
    have h := hG.dotProduct_mulVec_pos hx
    rw [star_trivial] at h
    rw [gramEval_eq_dotProduct]
    exact h

@[simp] theorem ofPosDef_gram (G : Matrix ι ι ℤ)
    (hG : (G.map (Int.cast : ℤ → ℝ)).PosDef) : (ofPosDef G hG).gram = G :=
  rfl

/-- `ofPosDef G hG` represents `n` exactly when `x ⬝ᵥ G *ᵥ x = n` for some
integer vector `x`. -/
theorem ofPosDef_represents_iff (G : Matrix ι ι ℤ)
    (hG : (G.map (Int.cast : ℤ → ℝ)).PosDef) (n : ℕ) :
    (ofPosDef G hG).Represents n ↔ ∃ x : ι → ℤ, x ⬝ᵥ G *ᵥ x = (n : ℤ) := by
  simp [Represents, eval_eq_dotProduct]

end Form

/-! ### Fibonacci-universality -/

/-- Fibonacci-universality: `P` represents every Fibonacci number. Including
`F₀ = 0` changes nothing, since every form represents 0. -/
def FibonacciUniversal (P : Form ι) : Prop :=
  ∀ n : ℕ, P.Represents (Nat.fib n)

/-- The forcing property of a Fibonacci criterion set: every form that
represents each element of `S`, in any finite rank, is Fibonacci-universal.
`IsFibonacciCriterionSet` in `Statement` adds that `S` is a finite set of
Fibonacci numbers of positive index. -/
def IsFibonacciCriterion (S : Set ℕ) : Prop :=
  ∀ (κ : Type) [Fintype κ] (P : Form κ),
    (∀ s ∈ S, P.Represents s) → FibonacciUniversal P

end FibonacciCriterion
