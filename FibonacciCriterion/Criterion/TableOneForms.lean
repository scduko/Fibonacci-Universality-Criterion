import FibonacciCriterion.Forms
import FibonacciCriterion.Criterion.TableOne

/-!
# The escalators of Table 1 as positive-definite forms

The rows of `tableOne` store each escalator `P_t` as a polynomial in
three variables, with coefficient 0 for the unused coordinates when the
rank is less than 3. This file removes those coordinates and builds `P_t` as a
positive-definite `Form` of its rank: the zero form, `⟨1⟩`, `⟨1,1⟩`, `⟨1,2⟩`,
`f`, and five diagonal ternary forms (`tableOneRow_realizable`).
-/

namespace FibonacciCriterion

namespace TableOneForms

/-- The zero form, of rank 0. -/
def zero : Form (Fin 0) :=
  Form.diagonal (fun _ => (1 : ℤ)) (fun _ => by norm_num)

/-- The unary form `⟨a⟩`, for `a > 0`. -/
def unary (a : ℤ) (ha : 0 < a) : Form (Fin 1) :=
  Form.diagonal (fun _ => a) (fun _ => ha)

/-- The diagonal binary form `⟨a, b⟩`, for `a, b > 0`. -/
def binary (a b : ℤ) (ha : 0 < a) (hb : 0 < b) : Form (Fin 2) :=
  Form.diagonal ![a, b] (by
    intro i
    fin_cases i
    · exact ha
    · exact hb)

/-- The diagonal ternary form `⟨a, b, c⟩`, for `a, b, c > 0`. -/
def ternary (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Form (Fin 3) :=
  Form.diagonal ![a, b, c] (by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc)

theorem unary_eval (a : ℤ) (ha : 0 < a) (x : Fin 1 → ℤ) :
    (unary a ha).eval x = a * x 0 ^ 2 := by
  simp [unary]

theorem binary_eval (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (x : Fin 2 → ℤ) :
    (binary a b ha hb).eval x = a * x 0 ^ 2 + b * x 1 ^ 2 := by
  simp [binary, Fin.sum_univ_succ]

theorem ternary_eval (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (x : Fin 3 → ℤ) :
    (ternary a b c ha hb hc).eval x =
      a * x 0 ^ 2 + b * x 1 ^ 2 + c * x 2 ^ 2 := by
  simp [ternary, Fin.sum_univ_succ, add_assoc]

theorem zero_represents_iff (n : ℕ) :
    zero.Represents n ↔ ∃ _v : IntTriple, (0 : ℤ) = (n : ℤ) := by
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : x = 0 := by
      funext i
      exact Fin.elim0 i
    refine ⟨(0, 0, 0), ?_⟩
    rw [hx0, Form.eval_zero] at hx
    exact hx
  · rintro ⟨_, hn⟩
    exact ⟨0, (Form.eval_zero zero).trans hn⟩

theorem unary_represents_iff (a : ℤ) (ha : 0 < a) (n : ℕ) :
    (unary a ha).Represents n ↔
      ∃ v : IntTriple, a * v.1 ^ 2 = (n : ℤ) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(x 0, 0, 0), ?_⟩
    rw [unary_eval] at hx
    exact hx
  · rintro ⟨v, hv⟩
    refine ⟨fun _ => v.1, ?_⟩
    rw [unary_eval]
    exact hv

theorem binary_represents_iff (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (binary a b ha hb).Represents n ↔
      ∃ v : IntTriple, a * v.1 ^ 2 + b * v.2.1 ^ 2 = (n : ℤ) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(x 0, x 1, 0), ?_⟩
    rw [binary_eval] at hx
    exact hx
  · rintro ⟨v, hv⟩
    refine ⟨![v.1, v.2.1], ?_⟩
    rw [binary_eval]
    exact hv

theorem ternary_represents_iff (a b c : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (n : ℕ) :
    (ternary a b c ha hb hc).Represents n ↔
      ∃ v : IntTriple, a * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = (n : ℤ) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(x 0, x 1, x 2), ?_⟩
    rw [ternary_eval] at hx
    exact hx
  · rintro ⟨v, hv⟩
    refine ⟨![v.1, v.2.1, v.2.2], ?_⟩
    rw [ternary_eval]
    exact hv

/-- The Gram matrix `[[1,0,0],[0,2,1],[0,1,4]]` of `f`. -/
def irregularGram : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; 0, 2, 1; 0, 1, 4]

theorem irregularGram_eval {R : Type*} [CommRing R] (x : Fin 3 → R) :
    gramEval (Matrix.of fun i j => (irregularGram i j : R)) x =
      x 0 ^ 2 + 2 * x 1 ^ 2 + 2 * x 1 * x 2 + 4 * x 2 ^ 2 := by
  simp [gramEval, irregularGram, Fin.sum_univ_succ]
  ring

/-- The escalator `f = x² + 2y² + 2yz + 4z²` of determinant 7, as a positive-definite
form. -/
def irregular : Form (Fin 3) where
  gram := irregularGram
  symmetric := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  positive := by
    intro x hx
    rw [irregularGram_eval]
    by_contra! h
    have h0 : x 0 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0), sq_nonneg (2 * x 1 + x 2), sq_nonneg (x 2)]
    have h2 : x 2 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0), sq_nonneg (2 * x 1 + x 2), sq_nonneg (x 2)]
    have hx0 : x 0 = 0 := sq_eq_zero_iff.mp h0
    have hx2 : x 2 = 0 := sq_eq_zero_iff.mp h2
    rw [hx0, hx2] at h
    have h1 : x 1 ^ 2 = 0 := by nlinarith [sq_nonneg (x 1)]
    have hx1 : x 1 = 0 := sq_eq_zero_iff.mp h1
    apply hx
    funext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2

theorem irregular_eval (x : Fin 3 → ℤ) :
    irregular.eval x =
      x 0 ^ 2 + 2 * x 1 ^ 2 + 2 * x 1 * x 2 + 4 * x 2 ^ 2 :=
  irregularGram_eval (R := ℤ) x

theorem irregular_represents_iff (n : ℕ) :
    irregular.Represents n ↔
      ∃ v : IntTriple,
        v.1 ^ 2 + 2 * v.2.1 ^ 2 + 2 * v.2.1 * v.2.2 + 4 * v.2.2 ^ 2 = (n : ℤ) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(x 0, x 1, x 2), ?_⟩
    rw [irregular_eval] at hx
    exact hx
  · rintro ⟨v, hv⟩
    refine ⟨![v.1, v.2.1, v.2.2], ?_⟩
    rw [irregular_eval]
    exact hv

end TableOneForms

/-- For each row of Table 1, some positive-definite form represents `n` if and
only if the row's polynomial takes the value `n`. The proof takes the form
`P_t` of rank `r ≤ 3`, without the unused coordinates. -/
theorem tableOneRow_realizable (i : Fin 10) :
    ∃ (r : ℕ) (P : Form (Fin r)), ∀ n : ℕ,
      P.Represents n ↔ ∃ v : IntTriple, (tableOneRow i).eval v = (n : ℤ) := by
  fin_cases i
  · refine ⟨0, TableOneForms.zero, ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.zero_represents_iff n
  · refine ⟨1, TableOneForms.unary 1 (by norm_num), ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.unary_represents_iff 1 (by norm_num) n
  · refine ⟨2, TableOneForms.binary 1 1 (by norm_num) (by norm_num), ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.binary_represents_iff 1 1 (by norm_num) (by norm_num) n
  · refine ⟨2, TableOneForms.binary 1 2 (by norm_num) (by norm_num), ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.binary_represents_iff 1 2 (by norm_num) (by norm_num) n
  · refine ⟨3, TableOneForms.irregular, ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.irregular_represents_iff n
  · refine ⟨3, TableOneForms.ternary 1 1 1 (by norm_num) (by norm_num) (by norm_num), ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.ternary_represents_iff 1 1 1 (by norm_num) (by norm_num) (by norm_num) n
  · refine ⟨3, TableOneForms.ternary 1 2 5 (by norm_num) (by norm_num) (by norm_num), ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.ternary_represents_iff 1 2 5 (by norm_num) (by norm_num) (by norm_num) n
  · refine ⟨3, TableOneForms.ternary 1 1 3 (by norm_num) (by norm_num) (by norm_num), ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.ternary_represents_iff 1 1 3 (by norm_num) (by norm_num) (by norm_num) n
  · refine ⟨3, TableOneForms.ternary 1 2 3 (by norm_num) (by norm_num) (by norm_num), ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.ternary_represents_iff 1 2 3 (by norm_num) (by norm_num) (by norm_num) n
  · refine ⟨3, TableOneForms.ternary 1 1 2 (by norm_num) (by norm_num) (by norm_num), ?_⟩
    intro n
    simpa [tableOneRow, tableOne, TableOneRow.eval]
      using TableOneForms.ternary_represents_iff 1 1 2 (by norm_num) (by norm_num) (by norm_num) n

end FibonacciCriterion
