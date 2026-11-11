import FibonacciCriterion.Forms.TernaryGram

/-!
# Quaternary extensions and their orthogonal sublattices (Lemmas 4.1 and 4.2)

A quaternary extension `M = T + ℤv` of a ternary lattice `T` with Gram matrix
`G_T` is recorded, as in §4.1 of the manuscript, by the pairings
`cᵢ = β_M(v, bᵢ)` and the norm `m = Q(v)`:
`Gram(M) = [[G_T, c], [cᵀ, m]]`.

The file first adds to `TernaryGram` the diagonal lattices
(`TernaryGram.diag`), positive definiteness (`TernaryGram.PosDef`), and
multiplication by `G_T` and by its adjugate. It then proves the parts of §4.1
that hold for every ternary `T`:

* replacing `v` by `v + x` with `x ∈ T` changes `c` to `c + G_T x` without
  changing the represented values (`shift`, `represents_shift_iff`); for
  diagonal `T = ⟨1, B, C⟩` this gives the representatives of Table 2
  (`exists_shift_diag`);
* Lemma 4.1: with `D = det G_T`, `α = adj(G_T) c`, and
  `gcdα = gcd(D, α₁, α₂, α₃)`, the integer `d = D / gcdα` (`index`) and the
  vector `β = α / gcdα` satisfy `G_T β = d c`, so the integral vector
  `w⊥ = (-β, d)` is orthogonal to `T` and has norm `q > 0`. Hence `T ⊥ ⟨q⟩ ⊆ M`
  (`eval_orthogonal`, `q_pos`). That this sublattice has index `d` in `M` is
  not proven; only the containment is used.
  Part (ii), equation (2), is `scaled_eval`:
  `d² Q_M(x, w) = Q_T(d x + w β) + q w²`. Part (iii) is `represents_of_sub`;
* Lemma 4.2: `d` divides `D` (`det_eq`), and if `M` represents a value `τ`
  omitted by `T`, then `d² τ = Q_T(y) + q k²` for some `y ∈ T` and `k ≥ 1`
  (equation (3), `exists_truant_equation`). Hence `q ≤ d² τ` (the bound (4),
  `δ ≤ τ`; `q_le_index_sq_mul`), `q ≤ D² τ` (the bound (5);
  `q_le_det_sq_mul`), and `D m ≤ D τ + cᵀ adj(G_T) c` (`det_mul_m_le`);
* `d` and `q` do not depend on the chosen generator (`index_shift`, `q_shift`).

The manuscript defines `d` as the least positive integer with
`d G_T⁻¹ c ∈ ℤ³`. This equals `D / gcd(D, α)`, but the characterization is not
proven here and nothing uses it.
-/

namespace FibonacciCriterion

namespace TernaryGram

/-- The diagonal ternary lattice `⟨a, b, c⟩`. -/
def diag (a b c : ℤ) : TernaryGram := ⟨a, b, c, 0, 0, 0⟩

@[simp] theorem diag_eval (a b c x y z : ℤ) :
    (diag a b c).eval x y z = a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
  simp [diag, eval]

@[simp] theorem diag_det (a b c : ℤ) : (diag a b c).det = a * b * c := by
  simp [diag, det]

/-- Positive definiteness of `T`: every nonzero integral vector has positive
value. The proofs use this integral statement; `Form` (in `Forms.lean`) asks
for positivity of the real form. -/
def PosDef (T : TernaryGram) : Prop :=
  ∀ x y z : ℤ, ¬ (x = 0 ∧ y = 0 ∧ z = 0) → 0 < T.eval x y z

theorem PosDef.eval_nonneg {T : TernaryGram} (hT : T.PosDef) (x y z : ℤ) :
    0 ≤ T.eval x y z := by
  by_cases h : x = 0 ∧ y = 0 ∧ z = 0
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp [eval]
  · exact (hT x y z h).le

/-- A diagonal lattice with positive entries is positive definite. -/
theorem diag_posDef {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (diag a b c).PosDef := by
  intro x y z h
  rw [diag_eval]
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · have hz : z ≠ 0 := fun hz => h ⟨hx, hy, hz⟩
      have := pow_pos (abs_pos.2 hz) 2
      rw [sq_abs] at this
      positivity
    · have := pow_pos (abs_pos.2 hy) 2
      rw [sq_abs] at this
      positivity
  · have := pow_pos (abs_pos.2 hx) 2
    rw [sq_abs] at this
    positivity

/-- The first coordinate of `G_T (x, y, z)`. -/
def mul₁ (T : TernaryGram) (x y z : ℤ) : ℤ := T.a * x + T.r * y + T.s * z

/-- The second coordinate of `G_T (x, y, z)`. -/
def mul₂ (T : TernaryGram) (x y z : ℤ) : ℤ := T.r * x + T.b * y + T.t * z

/-- The third coordinate of `G_T (x, y, z)`. -/
def mul₃ (T : TernaryGram) (x y z : ℤ) : ℤ := T.s * x + T.t * y + T.c * z

/-- The first coordinate of `adj(G_T) (x, y, z)`. -/
def adj₁ (T : TernaryGram) (x y z : ℤ) : ℤ :=
  (T.b * T.c - T.t ^ 2) * x + (T.s * T.t - T.c * T.r) * y +
    (T.r * T.t - T.b * T.s) * z

/-- The second coordinate of `adj(G_T) (x, y, z)`. -/
def adj₂ (T : TernaryGram) (x y z : ℤ) : ℤ :=
  (T.s * T.t - T.c * T.r) * x + (T.a * T.c - T.s ^ 2) * y +
    (T.r * T.s - T.a * T.t) * z

/-- The third coordinate of `adj(G_T) (x, y, z)`. -/
def adj₃ (T : TernaryGram) (x y z : ℤ) : ℤ :=
  (T.r * T.t - T.b * T.s) * x + (T.r * T.s - T.a * T.t) * y +
    (T.a * T.b - T.r ^ 2) * z

/-- `G_T adj(G_T) = det(G_T) I`, first coordinate. -/
theorem mul₁_adj (T : TernaryGram) (x y z : ℤ) :
    T.mul₁ (T.adj₁ x y z) (T.adj₂ x y z) (T.adj₃ x y z) = T.det * x := by
  simp only [mul₁, adj₁, adj₂, adj₃, det]
  ring

/-- `G_T adj(G_T) = det(G_T) I`, second coordinate. -/
theorem mul₂_adj (T : TernaryGram) (x y z : ℤ) :
    T.mul₂ (T.adj₁ x y z) (T.adj₂ x y z) (T.adj₃ x y z) = T.det * y := by
  simp only [mul₂, adj₁, adj₂, adj₃, det]
  ring

/-- `G_T adj(G_T) = det(G_T) I`, third coordinate. -/
theorem mul₃_adj (T : TernaryGram) (x y z : ℤ) :
    T.mul₃ (T.adj₁ x y z) (T.adj₂ x y z) (T.adj₃ x y z) = T.det * z := by
  simp only [mul₃, adj₁, adj₂, adj₃, det]
  ring

/-- `adj(G_T) G_T = det(G_T) I`, first coordinate. -/
theorem adj₁_mul (T : TernaryGram) (x y z : ℤ) :
    T.adj₁ (T.mul₁ x y z) (T.mul₂ x y z) (T.mul₃ x y z) = T.det * x := by
  simp only [mul₁, mul₂, mul₃, adj₁, det]
  ring

/-- `adj(G_T) G_T = det(G_T) I`, second coordinate. -/
theorem adj₂_mul (T : TernaryGram) (x y z : ℤ) :
    T.adj₂ (T.mul₁ x y z) (T.mul₂ x y z) (T.mul₃ x y z) = T.det * y := by
  simp only [mul₁, mul₂, mul₃, adj₂, det]
  ring

/-- `adj(G_T) G_T = det(G_T) I`, third coordinate. -/
theorem adj₃_mul (T : TernaryGram) (x y z : ℤ) :
    T.adj₃ (T.mul₁ x y z) (T.mul₂ x y z) (T.mul₃ x y z) = T.det * z := by
  simp only [mul₁, mul₂, mul₃, adj₃, det]
  ring

/-- The value `Q_T(x)` equals `x · G_T x`. -/
theorem eval_eq_mul (T : TernaryGram) (x y z : ℤ) :
    T.eval x y z = x * T.mul₁ x y z + y * T.mul₂ x y z + z * T.mul₃ x y z := by
  simp only [eval, mul₁, mul₂, mul₃]
  ring

end TernaryGram

/-- A quaternary extension `M = T + ℤv` of the ternary lattice `T`, recorded
by the pairings `cᵢ = β_M(v, bᵢ)` and the norm `m = Q(v)`. Positive
definiteness is a separate predicate, `QuaternaryExtension.PosDef`. -/
structure QuaternaryExtension (T : TernaryGram) where
  /-- The pairing `β_M(v, b₁)` of the generator with the first basis vector. -/
  c₁ : ℤ
  /-- The pairing `β_M(v, b₂)` of the generator with the second basis vector. -/
  c₂ : ℤ
  /-- The pairing `β_M(v, b₃)` of the generator with the third basis vector. -/
  c₃ : ℤ
  /-- The norm `m = Q(v)` of the generator. -/
  m : ℤ
deriving DecidableEq

namespace QuaternaryExtension

variable {T : TernaryGram} (M : QuaternaryExtension T)

/-- The quaternary Gram polynomial `Q_M(x, y, z, w)`. -/
def eval (x y z w : ℤ) : ℤ :=
  T.eval x y z + 2 * w * (M.c₁ * x + M.c₂ * y + M.c₃ * z) + M.m * w ^ 2

/-- `M` represents `n`: some integral vector has value `n`. -/
def Represents (n : ℤ) : Prop :=
  ∃ x y z w : ℤ, M.eval x y z w = n

/-- Positive definiteness of `M`: every nonzero integral vector has positive
value (the integral statement, as for `TernaryGram.PosDef`). -/
def PosDef : Prop :=
  ∀ x y z w : ℤ, ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) → 0 < M.eval x y z w

/-- `M` represents every Fibonacci number. -/
def FibonacciUniversal : Prop :=
  ∀ n : ℕ, M.Represents (Nat.fib n)

@[simp] theorem eval_zero_right (x y z : ℤ) : M.eval x y z 0 = T.eval x y z := by
  simp [eval]

/-- Every value of the ternary lattice is a value of the extension. -/
theorem represents_of_ternary {n : ℤ} (h : T.Represents n) : M.Represents n := by
  obtain ⟨x, y, z, h⟩ := h
  exact ⟨x, y, z, 0, by simpa using h⟩

theorem PosDef.eval_nonneg {M : QuaternaryExtension T} (hM : M.PosDef)
    (x y z w : ℤ) : 0 ≤ M.eval x y z w := by
  by_cases h : x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp [eval, TernaryGram.eval]
  · exact (hM x y z w h).le

/-- The generator of a positive-definite extension has positive norm. -/
theorem PosDef.m_pos {M : QuaternaryExtension T} (hM : M.PosDef) : 0 < M.m := by
  have := hM 0 0 0 1 (by simp)
  simpa [eval, TernaryGram.eval] using this

/-- A positive-definite extension contains a positive-definite ternary. -/
theorem PosDef.ternary {M : QuaternaryExtension T} (hM : M.PosDef) : T.PosDef := by
  intro x y z h
  have := hM x y z 0 (by tauto)
  simpa using this

/-! ### Changing the generator by a vector of `T` -/

/-- The extension with generator `v + a₁b₁ + a₂b₂ + a₃b₃`: the pairing
vector becomes `c + G_T a` and the norm becomes `Q_M(a, 1)`. -/
def shift (a₁ a₂ a₃ : ℤ) : QuaternaryExtension T where
  c₁ := M.c₁ + T.mul₁ a₁ a₂ a₃
  c₂ := M.c₂ + T.mul₂ a₁ a₂ a₃
  c₃ := M.c₃ + T.mul₃ a₁ a₂ a₃
  m := M.eval a₁ a₂ a₃ 1

theorem eval_shift (a₁ a₂ a₃ x y z w : ℤ) :
    (M.shift a₁ a₂ a₃).eval x y z w =
      M.eval (x + w * a₁) (y + w * a₂) (z + w * a₃) w := by
  simp only [shift, eval, TernaryGram.eval, TernaryGram.mul₁,
    TernaryGram.mul₂, TernaryGram.mul₃]
  ring

/-- Changing the generator by a vector of `T` does not change the
represented values. -/
theorem represents_shift_iff (a₁ a₂ a₃ : ℤ) {n : ℤ} :
    (M.shift a₁ a₂ a₃).Represents n ↔ M.Represents n := by
  constructor
  · rintro ⟨x, y, z, w, h⟩
    rw [eval_shift] at h
    exact ⟨_, _, _, _, h⟩
  · rintro ⟨x, y, z, w, h⟩
    refine ⟨x - w * a₁, y - w * a₂, z - w * a₃, w, ?_⟩
    rw [eval_shift]
    simpa using h

theorem fibonacciUniversal_shift_iff (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).FibonacciUniversal ↔ M.FibonacciUniversal := by
  simp only [FibonacciUniversal, represents_shift_iff]

theorem PosDef.shift {M : QuaternaryExtension T} (hM : M.PosDef)
    (a₁ a₂ a₃ : ℤ) : (M.shift a₁ a₂ a₃).PosDef := by
  intro x y z w h
  rw [eval_shift]
  apply hM
  rintro ⟨hx, hy, hz, rfl⟩
  apply h
  simp only [zero_mul, add_zero] at hx hy hz
  exact ⟨hx, hy, hz, rfl⟩

/-- For a diagonal ternary lattice, the shift moves each pairing coefficient
by a multiple of the corresponding diagonal entry. -/
theorem shift_diag (A B C : ℤ) (M : QuaternaryExtension (TernaryGram.diag A B C))
    (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).c₁ = M.c₁ + A * a₁ ∧
      (M.shift a₁ a₂ a₃).c₂ = M.c₂ + B * a₂ ∧
      (M.shift a₁ a₂ a₃).c₃ = M.c₃ + C * a₃ := by
  simp [shift, TernaryGram.diag, TernaryGram.mul₁, TernaryGram.mul₂,
    TernaryGram.mul₃]

/-- Representatives for `ℤ³ / G_T ℤ³` when `T = ⟨1, B, C⟩` is diagonal: the
pairing vector can be moved to `c₁ = 0`, `c₂ ∈ [o₂, o₂ + B)`,
`c₃ ∈ [o₃, o₃ + C)`. -/
theorem exists_shift_diag {B C : ℤ} (hB : 0 < B) (hC : 0 < C) (o₂ o₃ : ℤ)
    (M : QuaternaryExtension (TernaryGram.diag 1 B C)) :
    ∃ a₁ a₂ a₃ : ℤ, (M.shift a₁ a₂ a₃).c₁ = 0 ∧
      o₂ ≤ (M.shift a₁ a₂ a₃).c₂ ∧ (M.shift a₁ a₂ a₃).c₂ < o₂ + B ∧
      o₃ ≤ (M.shift a₁ a₂ a₃).c₃ ∧ (M.shift a₁ a₂ a₃).c₃ < o₃ + C := by
  refine ⟨-M.c₁, -((M.c₂ - o₂) / B), -((M.c₃ - o₃) / C), ?_⟩
  obtain ⟨h1, h2, h3⟩ := shift_diag 1 B C M (-M.c₁) (-((M.c₂ - o₂) / B))
    (-((M.c₃ - o₃) / C))
  rw [h1, h2, h3]
  have e2 := Int.emod_add_mul_ediv (M.c₂ - o₂) B
  have e3 := Int.emod_add_mul_ediv (M.c₃ - o₃) C
  have l2 := Int.emod_nonneg (M.c₂ - o₂) hB.ne'
  have u2 := Int.emod_lt_of_pos (M.c₂ - o₂) hB
  have l3 := Int.emod_nonneg (M.c₃ - o₃) hC.ne'
  have u3 := Int.emod_lt_of_pos (M.c₃ - o₃) hC
  refine ⟨by ring, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### Lemma 4.1: the orthogonal sublattice -/

/-- The first coordinate of `α = adj(G_T) c`. -/
def α₁ : ℤ := T.adj₁ M.c₁ M.c₂ M.c₃

/-- The second coordinate of `α = adj(G_T) c`. -/
def α₂ : ℤ := T.adj₂ M.c₁ M.c₂ M.c₃

/-- The third coordinate of `α = adj(G_T) c`. -/
def α₃ : ℤ := T.adj₃ M.c₁ M.c₂ M.c₃

/-- The greatest common divisor `gcd(det G_T, α₁, α₂, α₃)`. -/
def gcdα : ℕ := Int.gcd T.det (Int.gcd M.α₁ (Int.gcd M.α₂ M.α₃))

/-- The index `d = det(G_T) / gcd(det G_T, α)`. It is the least positive
integer with `d G_T⁻¹ c ∈ ℤ³`, the manuscript's definition of `d`; this
characterization is not proven here. -/
def index : ℤ := T.det / M.gcdα

/-- The first coordinate of `β = α / gcdα = d G_T⁻¹ c`. -/
def β₁ : ℤ := M.α₁ / M.gcdα

/-- The second coordinate of `β = α / gcdα = d G_T⁻¹ c`. -/
def β₂ : ℤ := M.α₂ / M.gcdα

/-- The third coordinate of `β = α / gcdα = d G_T⁻¹ c`. -/
def β₃ : ℤ := M.α₃ / M.gcdα

/-- The integer `q` of §4.1: the norm `Q_M(w⊥)` of the integral orthogonal
vector `w⊥ = d v - (β₁ b₁ + β₂ b₂ + β₃ b₃)`, so that `T ⊥ ⟨q⟩ ⊆ M`. -/
def q : ℤ := M.eval (-M.β₁) (-M.β₂) (-M.β₃) M.index

/-- The integer `cᵀ adj(G_T) c = c · α`, equal to `det(G_T) · cᵀ G_T⁻¹ c`. -/
def cα : ℤ := M.c₁ * M.α₁ + M.c₂ * M.α₂ + M.c₃ * M.α₃

theorem gcdα_dvd_det : (M.gcdα : ℤ) ∣ T.det := Int.gcd_dvd_left _ _

theorem gcdα_dvd_α₁ : (M.gcdα : ℤ) ∣ M.α₁ :=
  (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)

theorem gcdα_dvd_α₂ : (M.gcdα : ℤ) ∣ M.α₂ :=
  ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)).trans
    (Int.gcd_dvd_left _ _)

theorem gcdα_dvd_α₃ : (M.gcdα : ℤ) ∣ M.α₃ :=
  ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)).trans
    (Int.gcd_dvd_right _ _)

variable {M}

theorem gcdα_pos (hD : 0 < T.det) : 0 < (M.gcdα : ℤ) := by
  have : M.gcdα ≠ 0 := by
    simp only [gcdα, ne_eq, Int.gcd_eq_zero_iff, not_and]
    intro h
    omega
  omega

/-- Lemma 4.2, first assertion: `det G_T = gcd(det G_T, α) · d`, so `d` divides
`det G_T`. -/
theorem det_eq : T.det = M.gcdα * M.index := by
  rw [index, Int.mul_ediv_cancel' M.gcdα_dvd_det]

theorem α₁_eq : M.α₁ = M.gcdα * M.β₁ := by
  rw [β₁, Int.mul_ediv_cancel' M.gcdα_dvd_α₁]

theorem α₂_eq : M.α₂ = M.gcdα * M.β₂ := by
  rw [β₂, Int.mul_ediv_cancel' M.gcdα_dvd_α₂]

theorem α₃_eq : M.α₃ = M.gcdα * M.β₃ := by
  rw [β₃, Int.mul_ediv_cancel' M.gcdα_dvd_α₃]

theorem index_pos (hD : 0 < T.det) : 0 < M.index := by
  have hg := gcdα_pos (M := M) hD
  have h := det_eq (M := M)
  by_contra hd
  push Not at hd
  nlinarith

/-- `d ≤ det G_T`; this gives the bound (5) from (4). -/
theorem index_le_det (hD : 0 < T.det) : M.index ≤ T.det := by
  have hg := gcdα_pos (M := M) hD
  have hd := index_pos (M := M) hD
  rw [det_eq (M := M)]
  nlinarith

/-- `G_T β = d c`, first coordinate. -/
theorem mul₁_β (hD : 0 < T.det) : T.mul₁ M.β₁ M.β₂ M.β₃ = M.index * M.c₁ := by
  have hg := gcdα_pos (M := M) hD
  apply mul_left_cancel₀ hg.ne'
  have h := T.mul₁_adj M.c₁ M.c₂ M.c₃
  rw [← α₁, ← α₂, ← α₃, α₁_eq, α₂_eq, α₃_eq, det_eq (M := M)] at h
  simp only [TernaryGram.mul₁] at h ⊢
  linear_combination h

/-- `G_T β = d c`, second coordinate. -/
theorem mul₂_β (hD : 0 < T.det) : T.mul₂ M.β₁ M.β₂ M.β₃ = M.index * M.c₂ := by
  have hg := gcdα_pos (M := M) hD
  apply mul_left_cancel₀ hg.ne'
  have h := T.mul₂_adj M.c₁ M.c₂ M.c₃
  rw [← α₁, ← α₂, ← α₃, α₁_eq, α₂_eq, α₃_eq, det_eq (M := M)] at h
  simp only [TernaryGram.mul₂] at h ⊢
  linear_combination h

/-- `G_T β = d c`, third coordinate. -/
theorem mul₃_β (hD : 0 < T.det) : T.mul₃ M.β₁ M.β₂ M.β₃ = M.index * M.c₃ := by
  have hg := gcdα_pos (M := M) hD
  apply mul_left_cancel₀ hg.ne'
  have h := T.mul₃_adj M.c₁ M.c₂ M.c₃
  rw [← α₁, ← α₂, ← α₃, α₁_eq, α₂_eq, α₃_eq, det_eq (M := M)] at h
  simp only [TernaryGram.mul₃] at h ⊢
  linear_combination h

/-- `Q_M(X - kβ, k d) = Q_T(X) + q k²`: the vectors `X + k w⊥` realize
`T ⊥ ⟨q⟩` inside `M` (part of Lemma 4.1). -/
theorem eval_orthogonal (hD : 0 < T.det) (X₁ X₂ X₃ k : ℤ) :
    M.eval (X₁ - k * M.β₁) (X₂ - k * M.β₂) (X₃ - k * M.β₃) (k * M.index) =
      T.eval X₁ X₂ X₃ + M.q * k ^ 2 := by
  have h₁ := mul₁_β (M := M) hD
  have h₂ := mul₂_β (M := M) hD
  have h₃ := mul₃_β (M := M) hD
  simp only [q, eval, TernaryGram.eval]
  simp only [TernaryGram.mul₁, TernaryGram.mul₂, TernaryGram.mul₃] at h₁ h₂ h₃
  linear_combination (-2 * k * X₁) * h₁ + (-2 * k * X₂) * h₂ + (-2 * k * X₃) * h₃

/-- Lemma 4.1 (iii): `M` represents `N` whenever `T` represents `N - q k²` for
some integer `k`. -/
theorem represents_of_sub (hD : 0 < T.det) {N k : ℤ}
    (h : T.Represents (N - M.q * k ^ 2)) : M.Represents N := by
  obtain ⟨x, y, z, h⟩ := h
  refine ⟨x - k * M.β₁, y - k * M.β₂, z - k * M.β₃, k * M.index, ?_⟩
  rw [eval_orthogonal hD, h]
  ring

/-- Lemma 4.1 (ii), equation (2), the scaled inclusion `d M ⊆ T ⊥ ⟨q⟩`:
`d² Q_M(x, w) = Q_T(d x + w β) + q w²`. -/
theorem scaled_eval (hD : 0 < T.det) (x y z w : ℤ) :
    M.index ^ 2 * M.eval x y z w =
      T.eval (M.index * x + w * M.β₁) (M.index * y + w * M.β₂)
        (M.index * z + w * M.β₃) + M.q * w ^ 2 := by
  rw [← eval_orthogonal hD]
  simp only [eval, TernaryGram.eval]
  ring

/-- `q` is positive (part of Lemma 4.1). -/
theorem q_pos (hD : 0 < T.det) (hM : M.PosDef) : 0 < M.q := by
  apply hM
  have := index_pos (M := M) hD
  omega

/-- `det(G_T) q = d² (det(G_T) m - cᵀ adj(G_T) c)`, the integral form of
`q = d² δ` with the Schur complement `δ = m - cᵀ G_T⁻¹ c`. -/
theorem det_mul_q (hD : 0 < T.det) :
    T.det * M.q = M.index ^ 2 * (T.det * M.m - M.cα) := by
  have h₁ := mul₁_β (M := M) hD
  have h₂ := mul₂_β (M := M) hD
  have h₃ := mul₃_β (M := M) hD
  have e₁ := α₁_eq (M := M)
  have e₂ := α₂_eq (M := M)
  have e₃ := α₃_eq (M := M)
  have eD := det_eq (M := M)
  have hβ : T.eval M.β₁ M.β₂ M.β₃ =
      M.index * (M.c₁ * M.β₁ + M.c₂ * M.β₂ + M.c₃ * M.β₃) := by
    rw [TernaryGram.eval_eq_mul, h₁, h₂, h₃]
    ring
  have hq : M.q = M.m * M.index ^ 2 -
      M.index * (M.c₁ * M.β₁ + M.c₂ * M.β₂ + M.c₃ * M.β₃) := by
    have : T.eval (-M.β₁) (-M.β₂) (-M.β₃) = T.eval M.β₁ M.β₂ M.β₃ := by
      simp only [TernaryGram.eval]
      ring
    simp only [q, eval]
    rw [this, hβ]
    ring
  rw [hq, cα, e₁, e₂, e₃, eD]
  ring

/-- Lemma 4.2, equation (3): if `M` represents a value `τ` omitted by `T`,
then `d² τ = Q_T(y) + q k²` for some `y ∈ T` and some integer `k ≥ 1`. -/
theorem exists_truant_equation (hD : 0 < T.det) {τ : ℤ}
    (hτ : M.Represents τ) (hT : ¬ T.Represents τ) :
    ∃ y₁ y₂ y₃ k : ℤ, 1 ≤ k ∧
      M.index ^ 2 * τ = T.eval y₁ y₂ y₃ + M.q * k ^ 2 := by
  obtain ⟨x, y, z, w, h⟩ := hτ
  have hw : w ≠ 0 := by
    rintro rfl
    exact hT ⟨x, y, z, by simpa using h⟩
  -- Replace the vector by its negative if necessary, so that `k ≥ 1`.
  have hneg : M.eval (-x) (-y) (-z) (-w) = τ := by
    rw [← h]
    simp only [eval, TernaryGram.eval]
    ring
  rcases lt_or_gt_of_ne hw with hlt | hgt
  · have hs := scaled_eval (M := M) hD (-x) (-y) (-z) (-w)
    rw [hneg] at hs
    exact ⟨_, _, _, -w, by omega, hs⟩
  · have hs := scaled_eval (M := M) hD x y z w
    rw [h] at hs
    exact ⟨_, _, _, w, by omega, hs⟩

/-- The bound (4) of Lemma 4.2, `δ ≤ τ`, in the integral form `q ≤ d² τ`: this holds
for every extension representing a value `τ` omitted by `T`. -/
theorem q_le_index_sq_mul (hD : 0 < T.det) (hM : M.PosDef) {τ : ℤ}
    (hτ : M.Represents τ) (hT : ¬ T.Represents τ) :
    M.q ≤ M.index ^ 2 * τ := by
  obtain ⟨y₁, y₂, y₃, k, hk, h⟩ := exists_truant_equation hD hτ hT
  have hT0 := hM.ternary.eval_nonneg y₁ y₂ y₃
  have hq := q_pos hD hM
  have hk2 : 1 ≤ k ^ 2 := by nlinarith [mul_self_nonneg (k - 1)]
  rw [h]
  nlinarith [mul_nonneg hq.le (sub_nonneg.2 hk2)]

/-- The bound (5) of Lemma 4.2: an extension representing a value `τ` omitted by `T`
has `q ≤ τ det(G_T)²`. -/
theorem q_le_det_sq_mul (hD : 0 < T.det) (hM : M.PosDef) {τ : ℤ}
    (hτ : M.Represents τ) (hT : ¬ T.Represents τ) :
    M.q ≤ T.det ^ 2 * τ := by
  have h2 := q_le_index_sq_mul hD hM hτ hT
  have hd := index_pos (M := M) hD
  have hdD := index_le_det (M := M) hD
  have hτ0 : 0 ≤ τ := by
    obtain ⟨x, y, z, w, h⟩ := hτ
    rw [← h]
    exact hM.eval_nonneg x y z w
  have : M.index ^ 2 ≤ T.det ^ 2 := by
    apply pow_le_pow_left₀ hd.le hdD
  nlinarith

/-- The range of `m` in §4.1, `m ≤ ⌊τ + cᵀ G_T⁻¹ c⌋`, in the integral form
`det(G_T) m ≤ det(G_T) τ + cᵀ adj(G_T) c`, for an extension representing a
value `τ` omitted by `T`. -/
theorem det_mul_m_le (hD : 0 < T.det) (hM : M.PosDef) {τ : ℤ}
    (hτ : M.Represents τ) (hT : ¬ T.Represents τ) :
    T.det * M.m ≤ T.det * τ + M.cα := by
  have h2 := q_le_index_sq_mul hD hM hτ hT
  have h := det_mul_q (M := M) hD
  have hd := index_pos (M := M) hD
  have hd2 : 0 < M.index ^ 2 := by positivity
  have : M.index ^ 2 * (T.det * M.m - M.cα) ≤ M.index ^ 2 * (T.det * τ) := by
    rw [← h]
    nlinarith
  have := le_of_mul_le_mul_left this hd2
  linarith

/-! ### Independence of the chosen generator

The integers `d` and `q` depend only on the lattice `M`, not on the generator
`v`: replacing `v` by `v + a` changes `α` to `α + det(G_T) a`,
leaving `gcd(det G_T, α)` unchanged, and changes `β` to `β + d a`. -/

theorem dvd_gcdα_iff (M : QuaternaryExtension T) (n : ℕ) :
    n ∣ M.gcdα ↔ (n : ℤ) ∣ T.det ∧ (n : ℤ) ∣ M.α₁ ∧ (n : ℤ) ∣ M.α₂ ∧
      (n : ℤ) ∣ M.α₃ := by
  simp only [gcdα, Int.dvd_gcd_iff, Int.natCast_dvd_natCast]

theorem α₁_shift (M : QuaternaryExtension T) (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).α₁ = M.α₁ + T.det * a₁ := by
  have h := T.adj₁_mul a₁ a₂ a₃
  simp only [α₁, shift, TernaryGram.adj₁] at h ⊢
  linear_combination h

theorem α₂_shift (M : QuaternaryExtension T) (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).α₂ = M.α₂ + T.det * a₂ := by
  have h := T.adj₂_mul a₁ a₂ a₃
  simp only [α₂, shift, TernaryGram.adj₂] at h ⊢
  linear_combination h

theorem α₃_shift (M : QuaternaryExtension T) (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).α₃ = M.α₃ + T.det * a₃ := by
  have h := T.adj₃_mul a₁ a₂ a₃
  simp only [α₃, shift, TernaryGram.adj₃] at h ⊢
  linear_combination h

theorem gcdα_shift (M : QuaternaryExtension T) (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).gcdα = M.gcdα := by
  apply Nat.dvd_antisymm
  · rw [dvd_gcdα_iff]
    obtain ⟨h0, h1, h2, h3⟩ := ((M.shift a₁ a₂ a₃).dvd_gcdα_iff _).1 dvd_rfl
    rw [α₁_shift] at h1
    rw [α₂_shift] at h2
    rw [α₃_shift] at h3
    exact ⟨h0, (dvd_add_left (h0.mul_right _)).1 h1,
      (dvd_add_left (h0.mul_right _)).1 h2, (dvd_add_left (h0.mul_right _)).1 h3⟩
  · rw [dvd_gcdα_iff, α₁_shift, α₂_shift, α₃_shift]
    obtain ⟨h0, h1, h2, h3⟩ := (M.dvd_gcdα_iff _).1 dvd_rfl
    exact ⟨h0, h1.add (h0.mul_right _), h2.add (h0.mul_right _),
      h3.add (h0.mul_right _)⟩

/-- `d` does not depend on the chosen generator. -/
theorem index_shift (M : QuaternaryExtension T) (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).index = M.index := by
  simp only [index, gcdα_shift]

theorem β₁_shift (hD : 0 < T.det) (M : QuaternaryExtension T) (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).β₁ = M.β₁ + M.index * a₁ := by
  have hg := gcdα_pos (M := M) hD
  apply mul_left_cancel₀ hg.ne'
  have h := (M.shift a₁ a₂ a₃).α₁_eq
  rw [gcdα_shift, α₁_shift, M.α₁_eq, det_eq (M := M)] at h
  linear_combination -h

theorem β₂_shift (hD : 0 < T.det) (M : QuaternaryExtension T) (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).β₂ = M.β₂ + M.index * a₂ := by
  have hg := gcdα_pos (M := M) hD
  apply mul_left_cancel₀ hg.ne'
  have h := (M.shift a₁ a₂ a₃).α₂_eq
  rw [gcdα_shift, α₂_shift, M.α₂_eq, det_eq (M := M)] at h
  linear_combination -h

theorem β₃_shift (hD : 0 < T.det) (M : QuaternaryExtension T) (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).β₃ = M.β₃ + M.index * a₃ := by
  have hg := gcdα_pos (M := M) hD
  apply mul_left_cancel₀ hg.ne'
  have h := (M.shift a₁ a₂ a₃).α₃_eq
  rw [gcdα_shift, α₃_shift, M.α₃_eq, det_eq (M := M)] at h
  linear_combination -h

/-- `q` does not depend on the chosen generator. -/
theorem q_shift (hD : 0 < T.det) (M : QuaternaryExtension T) (a₁ a₂ a₃ : ℤ) :
    (M.shift a₁ a₂ a₃).q = M.q := by
  rw [q, eval_shift, index_shift, β₁_shift hD, β₂_shift hD, β₃_shift hD, q]
  congr 1 <;> ring_nf

end QuaternaryExtension

/-- Unfolds `index`, `β`, and `q` of an extension with explicit pairing
coefficients, so that `norm_num` evaluates the index and expresses `q` in
terms of `m`. -/
macro (name := quaternaryNorm) "quaternary_norm" : tactic =>
  `(tactic| norm_num [QuaternaryExtension.q, QuaternaryExtension.eval,
    QuaternaryExtension.β₁, QuaternaryExtension.β₂, QuaternaryExtension.β₃,
    QuaternaryExtension.index, QuaternaryExtension.gcdα,
    QuaternaryExtension.α₁, QuaternaryExtension.α₂, QuaternaryExtension.α₃,
    QuaternaryExtension.cα, TernaryGram.adj₁, TernaryGram.adj₂,
    TernaryGram.adj₃, TernaryGram.det, TernaryGram.diag, TernaryGram.eval])

end FibonacciCriterion
