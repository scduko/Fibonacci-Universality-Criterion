import FibonacciCriterion.Criterion.Theorem

/-!
# An example: `x² + 2y² + 5z² + 5w²`

The form `x² + 2y² + 5z² + 5w²` does not represent 15
(`not_represents_fifteen`), so it is not universal. It represents the ten
elements of `criterion` (`represents_criterion`, by explicit vectors), so by
Theorem 1.1 it represents every Fibonacci number (`fibonacciUniversal`).
-/

namespace FibonacciCriterion.Example

/-- The form `x² + 2y² + 5z² + 5w²`. -/
def form : Form (Fin 4) :=
  Form.diagonal ![1, 2, 5, 5] (by intro i; fin_cases i <;> simp)

/-- The value of `form` at `(x₀, x₁, x₂, x₃)`. -/
theorem form_eval (x : Fin 4 → ℤ) :
    form.eval x = x 0 ^ 2 + 2 * x 1 ^ 2 + 5 * x 2 ^ 2 + 5 * x 3 ^ 2 := by
  simp [form, Fin.sum_univ_four]

/-- The form does not represent 15: the equation bounds the coordinates, and
no vector in the resulting box has value 15. -/
theorem not_represents_fifteen : ¬ form.Represents 15 := by
  rintro ⟨x, hx⟩
  rw [form_eval] at hx
  push_cast at hx
  generalize x 0 = a at hx
  generalize x 1 = b at hx
  generalize x 2 = c at hx
  generalize x 3 = d at hx
  have ha2 : a ^ 2 ≤ 15 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb2 : b ^ 2 ≤ 7 := by nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  have hc2 : c ^ 2 ≤ 3 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
  have hd2 : d ^ 2 ≤ 3 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have ha : -3 ≤ a ∧ a ≤ 3 := by constructor <;> nlinarith
  have hb : -2 ≤ b ∧ b ≤ 2 := by constructor <;> nlinarith
  have hc : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith
  have hd : -1 ≤ d ∧ d ≤ 1 := by constructor <;> nlinarith
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  obtain ⟨hc₁, hc₂⟩ := hc
  obtain ⟨hd₁, hd₂⟩ := hd
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    interval_cases d <;> norm_num at hx

/-- The form represents every element of `criterion`. -/
theorem represents_criterion : ∀ t ∈ criterion, form.Represents t := by
  intro t ht
  simp only [criterion, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨![1, 0, 0, 0], by norm_num [form_eval]⟩
  · exact ⟨![0, 1, 0, 0], by norm_num [form_eval]⟩
  · exact ⟨![1, 1, 0, 0], by norm_num [form_eval]⟩
  · exact ⟨![0, 0, 1, 0], by norm_num [form_eval]⟩
  · exact ⟨![4, 0, 1, 0], by norm_num [form_eval]⟩
  · exact ⟨![0, 5, 1, 0], by norm_num [form_eval]⟩
  · exact ⟨![20, 10, 1, 1], by norm_num [form_eval]⟩
  · exact ⟨![10, 21, 1, 0], by norm_num [form_eval]⟩
  · exact ⟨![910, 40, 12, 2], by norm_num [form_eval]⟩
  · exact ⟨![12921, 7105, 1, 0], by norm_num [form_eval]⟩

/-- The form is Fibonacci-universal, by Theorem 1.1. -/
theorem fibonacciUniversal : FibonacciUniversal form :=
  (fibonacci_criterion.1 form).2 represents_criterion

end FibonacciCriterion.Example
