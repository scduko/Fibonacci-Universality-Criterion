import FibonacciCriterion.Forms.QuaternaryExtension
import FibonacciCriterion.Escalation.Pairing

/-!
# Quaternary escalations inside an ambient form (Lemma 3.6)

Let `Q` be a positive-definite integral form of any finite rank, let
`e₁, e₂, e₃` be vectors of `Q` with Gram matrix `G_T` (a frame of `T`,
`Form.IsFrame`), and let `u` be a vector of norm `τ`. The vectors
`x e₁ + y e₂ + z e₃ + w u` realize the quaternary extension `T + ℤu`
(`Form.extension`) with pairing vector `cᵢ = β(u, eᵢ)` and norm `m = τ`.

If `T` is positive definite and omits every value `k² τ` with `k ≠ 0` (the
integral form of "`τ` is not represented by `T ⊗ ℚ`" in Lemma 3.6), then this
extension is positive definite, so it has rank 4 (`extension_posDef`). The
proof does not need the frame or the extension to be primitive in the ambient
lattice. Every value of the extension is a value of `Q`
(`represents_of_extension`), so Fibonacci-universality of the extension gives
Fibonacci-universality of `Q` (`fibonacciUniversal_of_extension`).
`fibonacciUniversal_of_frame` combines the steps: if `Q` contains a frame of
`T` and represents `τ`, and every positive-definite extension of `T`
representing `τ` is Fibonacci-universal, then so is `Q`.
-/

namespace FibonacciCriterion

namespace Form

variable {ι : Type} [Fintype ι]

/-- A frame of `T` in `Q`: three vectors `e₁, e₂, e₃` whose Gram matrix under
`Q` is `G_T`. -/
def IsFrame (Q : Form ι) (T : TernaryGram) (e₁ e₂ e₃ : ι → ℤ) : Prop :=
  Q.eval e₁ = T.a ∧ Q.eval e₂ = T.b ∧ Q.eval e₃ = T.c ∧
    Q.pairing e₁ e₂ = T.r ∧ Q.pairing e₁ e₃ = T.s ∧ Q.pairing e₂ e₃ = T.t

/-- The quaternary extension `T + ℤu` realized inside `Q` by a frame of `T`
and a vector `u`, with `cᵢ = β(u, eᵢ)` and `m = Q(u)`. -/
def extension (Q : Form ι) (T : TernaryGram) (e₁ e₂ e₃ u : ι → ℤ) :
    QuaternaryExtension T where
  c₁ := Q.pairing u e₁
  c₂ := Q.pairing u e₂
  c₃ := Q.pairing u e₃
  m := Q.eval u

/-- For a frame of `T`, the value of the extension at `(x, y, z, w)` is
`Q(x e₁ + y e₂ + z e₃ + w u)`. -/
theorem extension_eval (Q : Form ι) {T : TernaryGram} {e₁ e₂ e₃ : ι → ℤ}
    (hf : Q.IsFrame T e₁ e₂ e₃) (u : ι → ℤ) (x y z w : ℤ) :
    (Q.extension T e₁ e₂ e₃ u).eval x y z w =
      Q.eval (x • e₁ + y • e₂ + z • e₃ + w • u) := by
  obtain ⟨h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := hf
  have h₂₁ : Q.pairing e₂ e₁ = T.r := (Q.pairing_comm _ _).trans h₁₂
  have h₃₁ : Q.pairing e₃ e₁ = T.s := (Q.pairing_comm _ _).trans h₁₃
  have h₃₂ : Q.pairing e₃ e₂ = T.t := (Q.pairing_comm _ _).trans h₂₃
  have hu₁ : Q.pairing e₁ u = Q.pairing u e₁ := Q.pairing_comm _ _
  have hu₂ : Q.pairing e₂ u = Q.pairing u e₂ := Q.pairing_comm _ _
  have hu₃ : Q.pairing e₃ u = Q.pairing u e₃ := Q.pairing_comm _ _
  have h₁' : Q.pairing e₁ e₁ = T.a := h₁
  have h₂' : Q.pairing e₂ e₂ = T.b := h₂
  have h₃' : Q.pairing e₃ e₃ = T.c := h₃
  have hu : Q.pairing u u = Q.eval u := rfl
  rw [show Q.eval (x • e₁ + y • e₂ + z • e₃ + w • u) =
      Q.pairing (x • e₁ + y • e₂ + z • e₃ + w • u)
        (x • e₁ + y • e₂ + z • e₃ + w • u) from rfl]
  simp only [pairing_add_left, pairing_add_right, pairing_smul_left,
    pairing_smul_right, h₁', h₂', h₃', h₁₂, h₁₃, h₂₃, h₂₁, h₃₁,
    h₃₂, hu₁, hu₂, hu₃, hu]
  simp only [extension, QuaternaryExtension.eval, TernaryGram.eval]
  ring

/-- For a frame of `T`, `Q_T(x, y, z) = Q(x e₁ + y e₂ + z e₃)`. -/
theorem frame_eval (Q : Form ι) {T : TernaryGram} {e₁ e₂ e₃ : ι → ℤ}
    (hf : Q.IsFrame T e₁ e₂ e₃) (x y z : ℤ) :
    T.eval x y z = Q.eval (x • e₁ + y • e₂ + z • e₃) := by
  have h := Q.extension_eval hf 0 x y z 0
  simpa using h

/-- Lemma 3.6 in integral form: if `T` is positive definite and omits every
nonzero square multiple of `Q(u)`, then `T + ℤu` is a positive-definite
quaternary extension. -/
theorem extension_posDef (Q : Form ι) {T : TernaryGram} {e₁ e₂ e₃ : ι → ℤ}
    (hf : Q.IsFrame T e₁ e₂ e₃) (hT : T.PosDef) (u : ι → ℤ)
    (hu : ∀ k : ℤ, k ≠ 0 → ¬ T.Represents (k ^ 2 * Q.eval u)) :
    (Q.extension T e₁ e₂ e₃ u).PosDef := by
  intro x y z w hne
  rw [Q.extension_eval hf]
  by_cases hv : x • e₁ + y • e₂ + z • e₃ + w • u = 0
  · exfalso
    by_cases hw : w = 0
    · subst hw
      have h0 : T.eval x y z = 0 := by
        rw [Q.frame_eval hf]
        simpa using congrArg Q.eval hv
      have hxyz : ¬ (x = 0 ∧ y = 0 ∧ z = 0) := by tauto
      have := hT x y z hxyz
      omega
    · apply hu w hw
      refine ⟨-x, -y, -z, ?_⟩
      have hvec : (-x) • e₁ + (-y) • e₂ + (-z) • e₃ = w • u := by
        rw [neg_smul, neg_smul, neg_smul, ← neg_add, ← neg_add,
          eq_neg_of_add_eq_zero_left hv, neg_neg]
      rw [Q.frame_eval hf, hvec, eval_smul]
  · exact Q.eval_pos _ hv

/-- The extension represents the norm `Q(u)` of its generator. -/
theorem extension_represents_norm (Q : Form ι) {T : TernaryGram}
    {e₁ e₂ e₃ : ι → ℤ} (hf : Q.IsFrame T e₁ e₂ e₃) (u : ι → ℤ) :
    (Q.extension T e₁ e₂ e₃ u).Represents (Q.eval u) := by
  refine ⟨0, 0, 0, 1, ?_⟩
  rw [Q.extension_eval hf]
  simp

/-- Values of an extension inside `Q` are values of `Q`. -/
theorem represents_of_extension (Q : Form ι) {T : TernaryGram}
    {e₁ e₂ e₃ : ι → ℤ} (hf : Q.IsFrame T e₁ e₂ e₃) (u : ι → ℤ) {n : ℕ}
    (h : (Q.extension T e₁ e₂ e₃ u).Represents n) : Q.Represents n := by
  obtain ⟨x, y, z, w, h⟩ := h
  exact ⟨x • e₁ + y • e₂ + z • e₃ + w • u, by rw [← Q.extension_eval hf, h]⟩

/-- Fibonacci-universality of an extension inside `Q` gives
Fibonacci-universality of `Q`. -/
theorem fibonacciUniversal_of_extension (Q : Form ι) {T : TernaryGram}
    {e₁ e₂ e₃ : ι → ℤ} (hf : Q.IsFrame T e₁ e₂ e₃) (u : ι → ℤ)
    (h : (Q.extension T e₁ e₂ e₃ u).FibonacciUniversal) :
    FibonacciUniversal Q :=
  fun n => Q.represents_of_extension hf u (h n)

/-- The escalation step of §7 for a ternary escalator: if `Q` contains a
frame of `T` and represents its truant `τ`, the extension `T + ℤu` by a
vector of norm `τ` is a positive-definite quaternary extension representing
`τ` (Lemma 3.6). If every such extension is Fibonacci-universal, so is `Q`. -/
theorem fibonacciUniversal_of_frame (Q : Form ι) {T : TernaryGram}
    {e₁ e₂ e₃ : ι → ℤ} (hf : Q.IsFrame T e₁ e₂ e₃) (hT : T.PosDef) {τ : ℕ}
    (homit : ∀ k : ℤ, k ≠ 0 → ¬ T.Represents (k ^ 2 * τ))
    (hclose : ∀ M : QuaternaryExtension T, M.PosDef → M.Represents τ →
      M.FibonacciUniversal)
    (hτ : Q.Represents τ) : FibonacciUniversal Q := by
  obtain ⟨u, hu⟩ := hτ
  apply Q.fibonacciUniversal_of_extension hf u
  apply hclose
  · exact Q.extension_posDef hf hT u (by rw [hu]; exact homit)
  · rw [← hu]
    exact Q.extension_represents_norm hf u

end Form

end FibonacciCriterion
