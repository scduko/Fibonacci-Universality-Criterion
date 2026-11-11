import FibonacciCriterion.Forms
import Mathlib.NumberTheory.SumFourSquares

/-!
# The four-square extension (§7)

For a form `P` that omits `t`, `fourSquareExtension P t` is the orthogonal sum
of `P`, four copies of `⟨t + 1⟩`, and `⟨j⟩` for each `j` with
`t + 1 ≤ j ≤ 2t + 1`. It still omits `t`, and by Lagrange's four-square
theorem it represents every integer greater than `t` (`exists_form_extension`).
This is the construction of Kim–Lee–Oh used in §7.

The index type `ι ⊕ (Fin 4 ⊕ Fin (t + 1))` stays symbolic: no matrix whose
size depends on `t` is evaluated.
-/

namespace FibonacciCriterion

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The index type of the summands added in the four-square extension: four
for the copies of `⟨t + 1⟩` and `t + 1` for `⟨t + 1⟩, …, ⟨2t + 1⟩`. -/
abbrev ExtensionIndex (t : ℕ) := Fin 4 ⊕ Fin (t + 1)

/-- The diagonal coefficients of the added summands: `t + 1` at each of the
four indices of `Fin 4`, and `t + 1 + j` at `j : Fin (t + 1)`. -/
def extensionWeight (t : ℕ) : ExtensionIndex t → ℤ
  | .inl _ => (t : ℤ) + 1
  | .inr j => (t : ℤ) + 1 + (j.val : ℤ)

theorem extensionWeight_pos (t : ℕ) (i : ExtensionIndex t) :
    0 < extensionWeight t i := by
  cases i <;> simp [extensionWeight]; omega

theorem extensionWeight_ge (t : ℕ) (i : ExtensionIndex t) :
    (t : ℤ) + 1 ≤ extensionWeight t i := by
  cases i <;> simp [extensionWeight]

/-- The added summands `⟨t + 1, t + 1, t + 1, t + 1⟩ ⊥ ⟨t + 1⟩ ⊥ ⋯ ⊥ ⟨2t + 1⟩`,
which represent every integer greater than `t`. -/
def extensionTail (t : ℕ) : Form (ExtensionIndex t) :=
  Form.diagonal (extensionWeight t) (extensionWeight_pos t)

theorem extensionTail_lower_bound (t : ℕ) (x : ExtensionIndex t → ℤ)
    (hx : x ≠ 0) : (t : ℤ) + 1 ≤ (extensionTail t).eval x :=
  Form.diagonal_lower_bound (extensionWeight t) (extensionWeight_pos t)
    ((t : ℤ) + 1) (extensionWeight_ge t) x hx

/-- The added summands represent every `N > t`: write `N = j + (t + 1) m` with
`t + 1 ≤ j ≤ 2t + 1`, and `m` as a sum of four squares (Lagrange). -/
theorem extensionTail_represents (t N : ℕ) (hN : t < N) :
    (extensionTail t).Represents N := by
  let k : ℕ := N - (t + 1)
  let m : ℕ := k / (t + 1)
  let r : Fin (t + 1) := ⟨k % (t + 1), Nat.mod_lt _ (by omega)⟩
  have hdecomp : N = t + 1 + (t + 1) * m + r.val := by
    have hmod := Nat.mod_add_div k (t + 1)
    have hsub : k + (t + 1) = N := Nat.sub_add_cancel (by omega)
    dsimp [m, r]
    omega
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares m
  let y : Fin 4 → ℤ := ![(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ)]
  let z : Fin (t + 1) → ℤ := fun j => if j = r then 1 else 0
  refine ⟨Sum.elim y z, ?_⟩
  have hz : (∑ j : Fin (t + 1),
      ((t : ℤ) + 1 + (j.val : ℤ)) * z j ^ 2) = (t : ℤ) + 1 + r.val := by
    rw [Finset.sum_eq_single r]
    · simp [z]
    · intro j _ hj
      simp [z, hj]
    · intro hr
      exact False.elim (hr (Finset.mem_univ r))
  have hsquares : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 +
      (d : ℤ) ^ 2 = (m : ℤ) := by
    exact_mod_cast habcd
  have hdecomp' : (N : ℤ) = (t : ℤ) + 1 + ((t : ℤ) + 1) * m + r.val := by
    exact_mod_cast hdecomp
  change (Form.diagonal (extensionWeight t) (extensionWeight_pos t)).eval
    (Sum.elim y z) = (N : ℤ)
  rw [Form.eval_diagonal, Fintype.sum_sum_type]
  change (∑ i : Fin 4, ((t : ℤ) + 1) * y i ^ 2) +
    (∑ j : Fin (t + 1), ((t : ℤ) + 1 + (j.val : ℤ)) * z j ^ 2) = (N : ℤ)
  rw [hz]
  simp [y, Fin.sum_univ_succ]
  rw [← hsquares] at hdecomp'
  nlinarith [hdecomp']

/-- The form `V_t = P ⊥ ⟨t + 1, t + 1, t + 1, t + 1⟩ ⊥ ⟨t + 1⟩ ⊥ ⋯ ⊥ ⟨2t + 1⟩`
of §7. -/
def fourSquareExtension (P : Form ι) (t : ℕ) : Form (ι ⊕ ExtensionIndex t) :=
  P.orthogonalSum (extensionTail t)

/-- `V_t` represents every number that `P` represents. -/
theorem fourSquareExtension_preserves (P : Form ι) (t n : ℕ)
    (h : P.Represents n) : (fourSquareExtension P t).Represents n :=
  Form.represents_orthogonalSum_left P (extensionTail t) h

/-- `V_t` represents every integer greater than `t`. -/
theorem fourSquareExtension_represents_above (P : Form ι) (t n : ℕ)
    (h : t < n) : (fourSquareExtension P t).Represents n :=
  Form.represents_orthogonalSum_right P (extensionTail t) (extensionTail_represents t n h)

/-- If `P` omits `t`, so does `V_t`: every nonzero vector of the added summands
has norm at least `t + 1`. -/
theorem fourSquareExtension_omits (P : Form ι) (t : ℕ)
    (ht : ¬ P.Represents t) : ¬ (fourSquareExtension P t).Represents t := by
  rintro ⟨x, hx⟩
  change (P.orthogonalSum (extensionTail t)).eval x = (t : ℤ) at hx
  rw [Form.eval_orthogonalSum] at hx
  by_cases hz : (fun j => x (.inr j)) = 0
  · apply ht
    refine ⟨fun i => x (.inl i), ?_⟩
    simpa [hz] using hx
  · have htail := extensionTail_lower_bound t (fun j => x (.inr j)) hz
    have hparent := P.eval_nonneg (fun i => x (.inl i))
    omega

/-- If `P` omits `t`, some form omits `t`, represents every number that `P`
represents, and represents every integer greater than `t`. -/
theorem exists_form_extension (P : Form ι) (t : ℕ) (ht : ¬ P.Represents t) :
    ∃ V : Form (ι ⊕ (Fin 4 ⊕ Fin (t + 1))),
      (¬ V.Represents t) ∧
      (∀ n, P.Represents n → V.Represents n) ∧
      (∀ n, t < n → V.Represents n) := by
  exact ⟨fourSquareExtension P t, fourSquareExtension_omits P t ht,
    fourSquareExtension_preserves P t, fourSquareExtension_represents_above P t⟩

end FibonacciCriterion
