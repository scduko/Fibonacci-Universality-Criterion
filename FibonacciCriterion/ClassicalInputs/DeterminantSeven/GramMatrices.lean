import FibonacciCriterion.ClassicalInputs.DeterminantSeven.BasisChange
import FibonacciCriterion.Irregular.Eligibility
import FibonacciCriterion.ClassicalInputs.Reduction.ReducedGram

/-!
# Representation by `f` or `h`: the Gram matrices (Proposition 3.3)

This file reduces the sufficiency direction of Proposition 3.3 to the choice
of an auxiliary prime. For an eligible positive integer `n` not divisible by
49, it is enough to construct a positive-definite integral ternary Gram matrix
of determinant 7 that represents `n` and has seven zeros modulo 7.
Minkowski reduction and the finite list of reduced Gram matrices of
determinant 7 then put the matrix in the class of `f` or `h`
(`represents_f_or_h_of_positive_det_seven_zeroCount`).

The file defines the two Gram matrices of the proof of Proposition 3.3,
`unramifiedGram` for `7 ∤ n` and `ramifiedGram` for `n = 7u`, and
proves their determinant, positivity, and zero count from the integer
identities satisfied by their entries. The existence of these entries is
stated as `UnramifiedSevenArithmetic` and `RamifiedSevenArithmetic`; the
choice of the auxiliary prime and the reciprocity arguments that prove them
are in `ClassicalInputs.DeterminantSeven.Unramified` and
`ClassicalInputs.DeterminantSeven.Ramified`. The manuscript distinguishes the
classes by its residue invariant, the square class of a binary determinant
modulo 7; here the invariant is the number of zeros modulo 7.
-/

namespace FibonacciCriterion.DeterminantSevenGenus

open TauCeti

/-- The Gram matrix `[[n, 1, L], [1, a, 0], [L, 0, c]]` of the case `7 ∤ n`.

`ClassicalInputs.DeterminantSeven.Unramified` chooses a prime `q > 7n` with
`q ≡ -1 (mod 8n)` and `q ≡ 1 (mod 7)`, a root `L² ≡ -7n (mod q)`,
`a = (q + 1)/n`, and `c = (7 + aL²)/q`. The manuscript's `ℓ`, `λ`, `a₀`, `c₀`
are `q`, `L`, `a`, `c`. -/
def unramifiedGram (n a L c : ℤ) : TernaryGram :=
  ⟨n, a, c, 1, L, 0⟩

/-- If `na = q + 1` and `qc = 7 + aL²`, the matrix has determinant 7. -/
theorem unramifiedGram_det {n q a L c : ℤ}
    (hna : n * a = q + 1) (hqc : q * c = 7 + a * L ^ 2) :
    (unramifiedGram n a L c).det = 7 := by
  simp only [unramifiedGram, TernaryGram.det]
  linear_combination c * hna + hqc

/-- The matrix represents `n`, its first diagonal entry. -/
theorem unramifiedGram_represents (n a L c : ℤ) :
    (unramifiedGram n a L c).Represents n := by
  exact ⟨1, 0, 0, by simp [unramifiedGram, TernaryGram.eval]⟩

/-- The matrix is positive definite: its leading principal minors are `n`,
`q = na - 1`, and 7. The proof uses the `LDLᵀ` decomposition with
denominators cleared. -/
theorem unramifiedGram_positive {n q a L c : ℤ}
    (hn : 0 < n) (hq : 0 < q)
    (hna : n * a = q + 1) (hdet : (unramifiedGram n a L c).det = 7) :
    ∀ x y z : ℤ, x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 →
      0 < (unramifiedGram n a L c).eval x y z := by
  intro x y z hxyz
  let Q := (unramifiedGram n a L c).eval x y z
  have hminor : n * a - 1 = q := by linarith
  have hid0 :
      n * (n * a - 1) * Q =
        (n * a - 1) * (n * x + y + L * z) ^ 2 +
          ((n * a - 1) * y - L * z) ^ 2 +
            n * (unramifiedGram n a L c).det * z ^ 2 := by
    dsimp [Q, unramifiedGram, TernaryGram.eval, TernaryGram.det]
    ring
  have hid :
      n * q * Q =
        q * (n * x + y + L * z) ^ 2 +
          (q * y - L * z) ^ 2 + n * 7 * z ^ 2 := by
    simpa only [hminor, hdet] using hid0
  have hright : 0 <
      q * (n * x + y + L * z) ^ 2 +
        (q * y - L * z) ^ 2 + n * 7 * z ^ 2 := by
    rcases hxyz with hx | hy | hz
    · by_cases hz0 : z = 0
      · subst z
        by_cases hy0 : y = 0
        · subst y
          have hs : 0 < (n * x) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hn.ne' hx)
          nlinarith [sq_nonneg (q * (n * x) ^ 2)]
        · have hs : 0 < (q * y) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hq.ne' hy0)
          nlinarith [sq_nonneg (n * x + y) ]
      · have hs : 0 < z ^ 2 := sq_pos_of_ne_zero hz0
        nlinarith [sq_nonneg (n * x + y + L * z), sq_nonneg (q * y - L * z)]
    · by_cases hz0 : z = 0
      · subst z
        have hs : 0 < (q * y) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hq.ne' hy)
        nlinarith [sq_nonneg (n * x + y)]
      · have hs : 0 < z ^ 2 := sq_pos_of_ne_zero hz0
        nlinarith [sq_nonneg (n * x + y + L * z), sq_nonneg (q * y - L * z)]
    · have hs : 0 < z ^ 2 := sq_pos_of_ne_zero hz
      nlinarith [sq_nonneg (n * x + y + L * z), sq_nonneg (q * y - L * z)]
  have hprod : 0 < n * q * Q := by rw [hid]; exact hright
  have hnq : 0 < n * q := mul_pos hn hq
  by_contra hQ
  have hQ' : Q ≤ 0 := le_of_not_gt hQ
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hnq.le hQ')) hprod

/-- The Gram matrix `[[7u, 7, -7d], [7, a, 0], [-7d, 0, c]]` of the case
`n = 7u`.

`ClassicalInputs.DeterminantSeven.Ramified` chooses a prime `p > 8u` with
`p ≡ -7 (mod 8u)`, a root `49d² ≡ -u (mod p)`, `a = (p + 7)/u`, and
`c = (1 + 7ad²)/p`. The manuscript's `ℓ`, `η`, `a₀`, `c₀` are `p`, `d`, `a`,
`c`; the manuscript takes `ℓ > 7u`. -/
def ramifiedGram (u a d c : ℤ) : TernaryGram :=
  ⟨7 * u, a, c, 7, -7 * d, 0⟩

/-- If `ua = p + 7` and `pc = 1 + 7ad²`, the matrix has determinant 7. -/
theorem ramifiedGram_det {u p a d c : ℤ}
    (hua : u * a = p + 7) (hpc : p * c = 1 + 7 * a * d ^ 2) :
    (ramifiedGram u a d c).det = 7 := by
  simp only [ramifiedGram, TernaryGram.det]
  linear_combination 7 * c * hua + 7 * hpc

/-- The matrix represents `7u`, its first diagonal entry. -/
theorem ramifiedGram_represents (u a d c : ℤ) :
    (ramifiedGram u a d c).Represents (7 * u) := by
  exact ⟨1, 0, 0, by simp [ramifiedGram, TernaryGram.eval]⟩

/-- The matrix is positive definite: its leading principal minors are `7u`,
`7p`, and 7. The proof is the same as for `unramifiedGram`. -/
theorem ramifiedGram_positive {u p a d c : ℤ}
    (hu : 0 < u) (hp : 0 < p)
    (hua : u * a = p + 7) (hdet : (ramifiedGram u a d c).det = 7) :
    ∀ x y z : ℤ, x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 →
      0 < (ramifiedGram u a d c).eval x y z := by
  intro x y z hxyz
  let Q := (ramifiedGram u a d c).eval x y z
  have hminor : (7 * u) * a - 7 ^ 2 = 7 * p := by nlinarith
  have hid0 :
      (7 * u) * ((7 * u) * a - 7 ^ 2) * Q =
        ((7 * u) * a - 7 ^ 2) * ((7 * u) * x + 7 * y - 7 * d * z) ^ 2 +
          (((7 * u) * a - 7 ^ 2) * y + 49 * d * z) ^ 2 +
            (7 * u) * (ramifiedGram u a d c).det * z ^ 2 := by
    dsimp [Q, ramifiedGram, TernaryGram.eval, TernaryGram.det]
    ring
  have hid :
      (7 * u) * (7 * p) * Q =
        (7 * p) * ((7 * u) * x + 7 * y - 7 * d * z) ^ 2 +
          ((7 * p) * y + 49 * d * z) ^ 2 + (7 * u) * 7 * z ^ 2 := by
    simpa only [hminor, hdet] using hid0
  have hn : 0 < 7 * u := by positivity
  have hq : 0 < 7 * p := by positivity
  have hright : 0 <
      (7 * p) * ((7 * u) * x + 7 * y - 7 * d * z) ^ 2 +
        ((7 * p) * y + 49 * d * z) ^ 2 + (7 * u) * 7 * z ^ 2 := by
    by_cases hz0 : z = 0
    · subst z
      by_cases hy0 : y = 0
      · subst y
        have hx : x ≠ 0 := by tauto
        have hs : 0 < ((7 * u) * x) ^ 2 :=
          sq_pos_of_ne_zero (mul_ne_zero hn.ne' hx)
        nlinarith [sq_nonneg ((7 * p) * ((7 * u) * x) ^ 2)]
      · have hs : 0 < ((7 * p) * y) ^ 2 :=
          sq_pos_of_ne_zero (mul_ne_zero hq.ne' hy0)
        nlinarith [sq_nonneg ((7 * u) * x + 7 * y)]
    · have hs : 0 < z ^ 2 := sq_pos_of_ne_zero hz0
      nlinarith [sq_nonneg ((7 * u) * x + 7 * y - 7 * d * z),
        sq_nonneg ((7 * p) * y + 49 * d * z)]
  have hprod : 0 < (7 * u) * (7 * p) * Q := by rw [hid]; exact hright
  have hnq : 0 < (7 * u) * (7 * p) := mul_pos hn hq
  by_contra hQ
  have hQ' : Q ≤ 0 := le_of_not_gt hQ
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hnq.le hQ')) hprod

/-! ## Zero counts modulo 7

The zero counts of the two matrices depend on at most four residues modulo
7, so the kernel checks them over all residues.
-/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unramified_zeroCount_residue :
    ∀ n a L c : ZMod 7,
      n * a = 2 → c = a * L ^ 2 →
        (Finset.univ.filter (fun v : Fin 3 → ZMod 7 =>
          n * v 0 ^ 2 + a * v 1 ^ 2 + c * v 2 ^ 2 +
            2 * v 0 * v 1 + 2 * L * v 0 * v 2 = 0)).card = 7 := by
  decide

/-- If `na ≡ 2` and `c ≡ aL² (mod 7)`, then `unramifiedGram` has seven
zeros modulo 7, as `f` and `h` do. -/
theorem unramifiedGram_zeroCount {n a L c : ℤ}
    (hna : (n : ZMod 7) * (a : ZMod 7) = 2)
    (hc : (c : ZMod 7) = (a : ZMod 7) * (L : ZMod 7) ^ 2) :
    modSevenZeroCount (unramifiedGram n a L c) = 7 := by
  simpa [modSevenZeroCount, modSevenZeros, TernaryGram.evalModSeven,
    unramifiedGram] using
      unramified_zeroCount_residue (n : ZMod 7) (a : ZMod 7)
        (L : ZMod 7) (c : ZMod 7) hna hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ramified_zeroCount_residue :
    ∀ a c : ZMod 7,
      (a * c = 1 ∨ a * c = 2 ∨ a * c = 4) →
        (Finset.univ.filter (fun v : Fin 3 → ZMod 7 =>
          a * v 1 ^ 2 + c * v 2 ^ 2 = 0)).card = 7 := by
  decide

/-- If `ac ≡ 1, 2, 4 (mod 7)`, then `ramifiedGram` has seven zeros
modulo 7. Modulo 7 its first row and column vanish, and the binary
block `diag(a, c)` has nonzero square determinant, so it is anisotropic and
the zeros are the seven vectors of the radical. -/
theorem ramifiedGram_zeroCount {u a d c : ℤ}
    (hac : (a : ZMod 7) * (c : ZMod 7) = 1 ∨
      (a : ZMod 7) * (c : ZMod 7) = 2 ∨
      (a : ZMod 7) * (c : ZMod 7) = 4) :
    modSevenZeroCount (ramifiedGram u a d c) = 7 := by
  have h7z : (7 : ZMod 7) = 0 := ZMod.natCast_self 7
  simpa [modSevenZeroCount, modSevenZeros, TernaryGram.evalModSeven,
    ramifiedGram, h7z] using
      ramified_zeroCount_residue (a : ZMod 7) (c : ZMod 7) hac

/-- A positive-definite Gram matrix of determinant 7 that represents `n`
and has seven zeros modulo 7. -/
structure SevenGramData (n : ℕ) where
  /-- The Gram matrix of determinant 7 that represents `n`. -/
  gram : TernaryGram
  represents : gram.Represents (n : ℤ)
  positive : ∀ x y z : ℤ, x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 → 0 < gram.eval x y z
  determinant : gram.det = 7
  zeroCount : modSevenZeroCount gram = 7

/-! ## Auxiliary-prime witnesses

Primality and reciprocity are used only to produce the following integers.
The passage from them to a positive-definite Gram matrix of determinant 7
is algebraic.
-/

/-- The integers produced by the auxiliary-prime construction when `7 ∤ n`:
`q > 0` with `q ≡ 1 (mod 7)`, `na = q + 1`, and `qc = 7 + aL²`. -/
structure UnramifiedWitness (n : ℕ) where
  /-- The auxiliary prime `q`. The structure records `q > 0` and
  `q ≡ 1 (mod 7)`, not primality. -/
  q : ℤ
  /-- The quotient `a = (q + 1)/n`, the second diagonal entry of
  `unramifiedGram`. -/
  a : ℤ
  /-- The root `L` of `L² ≡ -7n (mod q)`, an off-diagonal entry of
  `unramifiedGram`. -/
  L : ℤ
  /-- The quotient `c = (7 + aL²)/q`, the third diagonal entry of
  `unramifiedGram`. -/
  c : ℤ
  q_pos : 0 < q
  q_mod_seven : (q : ZMod 7) = 1
  quotient_a : (n : ℤ) * a = q + 1
  quotient_c : q * c = 7 + a * L ^ 2

/-- The integers produced by the auxiliary-prime construction when `n = 7u`
with `u > 0` and `u ≡ 1, 2, 4 (mod 7)`: `p > 0` with `ua = p + 7` and
`pc = 1 + 7ad²`. -/
structure RamifiedWitness (n : ℕ) where
  /-- The quotient `u = n/7`. -/
  u : ℕ
  /-- The quotient `a = (p + 7)/u`, the second diagonal entry of
  `ramifiedGram`. -/
  a : ℤ
  /-- The root `d` of `49d² ≡ -u (mod p)`; `-7d` is an off-diagonal entry of
  `ramifiedGram`. -/
  d : ℤ
  /-- The quotient `c = (1 + 7ad²)/p`, the third diagonal entry of
  `ramifiedGram`. -/
  c : ℤ
  /-- The auxiliary prime `p`. The structure records `p > 0`, not
  primality. -/
  p : ℤ
  input_eq : n = 7 * u
  u_pos : 0 < u
  p_pos : 0 < p
  u_square_mod_seven : (u : ZMod 7) = 1 ∨
    (u : ZMod 7) = 2 ∨ (u : ZMod 7) = 4
  quotient_a : (u : ℤ) * a = p + 7
  quotient_c : p * c = 1 + 7 * a * d ^ 2

set_option maxRecDepth 100000 in
private theorem ramified_binary_det_square_residue :
    ∀ u a p c : ZMod 7,
      (u = 1 ∨ u = 2 ∨ u = 4) → u * a = p → p * c = 1 →
        (a * c = 1 ∨ a * c = 2 ∨ a * c = 4) := by
  decide

/-- The matrix `unramifiedGram` built from an unramified witness, with
its properties. -/
def UnramifiedWitness.toGramData {n : ℕ} (hn : 0 < n)
    (w : UnramifiedWitness n) : SevenGramData n := by
  let A := unramifiedGram (n : ℤ) w.a w.L w.c
  have hdet : A.det = 7 :=
    unramifiedGram_det w.quotient_a w.quotient_c
  have hna7 : (n : ZMod 7) * (w.a : ZMod 7) = 2 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 7)) w.quotient_a
    norm_num [w.q_mod_seven] at h ⊢
    exact h
  have hc7 : (w.c : ZMod 7) = (w.a : ZMod 7) * (w.L : ZMod 7) ^ 2 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 7)) w.quotient_c
    push_cast at h
    have h7z : (7 : ZMod 7) = 0 := ZMod.natCast_self 7
    simpa only [w.q_mod_seven, one_mul, h7z, zero_add] using h
  exact
    { gram := A
      represents := unramifiedGram_represents _ _ _ _
      positive := unramifiedGram_positive
        (by exact_mod_cast hn) w.q_pos w.quotient_a hdet
      determinant := hdet
      zeroCount := unramifiedGram_zeroCount hna7 hc7 }

/-- The matrix `ramifiedGram` built from a ramified witness, with its
properties. -/
def RamifiedWitness.toGramData {n : ℕ}
    (w : RamifiedWitness n) : SevenGramData n := by
  let A := ramifiedGram (w.u : ℤ) w.a w.d w.c
  have hdet : A.det = 7 :=
    ramifiedGram_det w.quotient_a w.quotient_c
  have hua7 : (w.u : ZMod 7) * (w.a : ZMod 7) = (w.p : ZMod 7) := by
    have h := congrArg (fun z : ℤ => (z : ZMod 7)) w.quotient_a
    push_cast at h
    have h7z : (7 : ZMod 7) = 0 := ZMod.natCast_self 7
    simpa only [h7z, add_zero] using h
  have hpc7 : (w.p : ZMod 7) * (w.c : ZMod 7) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 7)) w.quotient_c
    push_cast at h
    have h7z : (7 : ZMod 7) = 0 := ZMod.natCast_self 7
    simpa only [h7z, zero_mul, zero_add, add_zero] using h
  have hac := ramified_binary_det_square_residue
    (w.u : ZMod 7) (w.a : ZMod 7) (w.p : ZMod 7) (w.c : ZMod 7)
    w.u_square_mod_seven hua7 hpc7
  have hrep : A.Represents (n : ℤ) := by
    rw [w.input_eq]
    push_cast
    exact ramifiedGram_represents _ _ _ _
  exact
    { gram := A
      represents := hrep
      positive := ramifiedGram_positive
        (by exact_mod_cast w.u_pos) w.p_pos w.quotient_a hdet
      determinant := hdet
      zeroCount := ramifiedGram_zeroCount hac }

/-- The statement that every `ResidualEligible` integer has an unramified or a
ramified witness. Dirichlet's theorem and quadratic reciprocity give the
unramified witness when `7 ∤ n` and the ramified one when `7 ∣ n`. It is proven
as `sevenArithmetic` in `ClassicalInputs.DeterminantSeven`. -/
def SevenArithmetic : Prop :=
  ∀ n : ℕ, Irregular.ResidualEligible n →
    Nonempty (UnramifiedWitness n) ∨
      Nonempty (RamifiedWitness n)

/-- The statement that every `ResidualEligible` integer `n` with `7 ∤ n` has an
unramified witness. It is proven as `unramifiedSevenArithmetic` in
`ClassicalInputs.DeterminantSeven.Unramified`. -/
def UnramifiedSevenArithmetic : Prop :=
  ∀ n : ℕ, Irregular.ResidualEligible n → n % 7 ≠ 0 →
    Nonempty (UnramifiedWitness n)

/-- The statement that every `ResidualEligible` integer `n` with `7 ∣ n`, that
is, with `v₇(n) = 1`, has a ramified witness. It is proven as
`ramifiedSevenArithmetic` in `ClassicalInputs.DeterminantSeven.Ramified`. -/
def RamifiedSevenArithmetic : Prop :=
  ∀ n : ℕ, Irregular.ResidualEligible n → n % 7 = 0 →
    Nonempty (RamifiedWitness n)

/-- The unramified and ramified cases together give
`SevenArithmetic`. -/
theorem sevenArithmetic_of_cases
    (hun : UnramifiedSevenArithmetic) (hram : RamifiedSevenArithmetic) :
    SevenArithmetic := by
  intro n hn
  by_cases h7 : n % 7 = 0
  · exact Or.inr (hram n hn h7)
  · exact Or.inl (hun n hn h7)

/-! ## The construction for every eligible integer -/

/-- The statement that every `ResidualEligible` integer has a `SevenGramData`.
The proof, `sevenGramConstruction` in `ClassicalInputs.DeterminantSeven`, uses
Dirichlet's theorem, quadratic reciprocity, the two Gram matrices above, and a
finite calculation modulo 7. -/
def SevenGramConstruction : Prop :=
  ∀ n : ℕ, Irregular.ResidualEligible n →
    Nonempty (SevenGramData n)

/-- `SevenArithmetic` implies `SevenGramConstruction`. -/
theorem sevenGramConstruction_of_arithmetic
    (h : SevenArithmetic) : SevenGramConstruction := by
  intro n hn
  rcases h n hn with hw | hw
  · rcases hw with ⟨w⟩
    exact ⟨w.toGramData hn.1⟩
  · rcases hw with ⟨w⟩
    exact ⟨w.toGramData⟩

/-! ## From the Gram matrix to f or h

The proof changes from the standard basis of `tauLattice A` to a
Minkowski-reduced basis, carries the zero count modulo 7 across the change
of basis, and applies the kernel-checked list of the fifteen reduced Gram
matrices of determinant 7.
-/

/-- The change from the standard basis of `tauLattice A` to a basis `b`,
reduced modulo 7: a `ModSevenIsometry` from `A` to the Gram matrix
of `b`. -/
noncomputable def modSevenIsometryToBasis (A : TernaryGram)
    (b : Module.Basis (Fin 3) ℤ (tauLattice A)) :
    ModSevenIsometry A (TernaryGram.ofBasis (tauLattice A) b) := by
  have h := modSevenIsometryOfBases (tauLattice A)
    (IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin 3)) A.matrix A.matrix_isSymm) b
  rw [ofBasis_canonical] at h
  exact h

/-- Every integer represented by a positive-definite integral ternary form of
determinant 7 with seven zeros modulo 7 is represented by `f`
or `h`. -/
theorem represents_f_or_h_of_positive_det_seven_zeroCount
    (A : TernaryGram)
    (hpos : ∀ x y z : ℤ, x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 → 0 < A.eval x y z)
    (hdet : A.det = 7) (hzero : modSevenZeroCount A = 7)
    {n : ℤ} (hrep : A.Represents n) :
    Irregular.RepresentsF n ∨ Irregular.RepresentsH n := by
  obtain ⟨b, hb⟩ := TernaryGram.exists_basis_isBoundedDeterminantCandidate
    (tauLattice A) (tauLattice_isPosDef A hpos) (tauLattice_finrank A) (7 : ℕ)
    ((tauLattice_determinant A).trans hdet)
  let G := TernaryGram.ofBasis (tauLattice A) b
  have hred : G ∈ reducedDetSeven := reducedList_seven ▸
    TernaryClassification.mem_reducedList_of_bounded
      (TernaryClassification.isBoundedCandidate_of_isBoundedDeterminantCandidate (by norm_num) hb)
  have hcount : modSevenZeroCount G = 7 := by
    calc
      modSevenZeroCount G = modSevenZeroCount A :=
        (modSevenZeroCount_eq_of_isometry (modSevenIsometryToBasis A b)).symm
      _ = 7 := hzero
  have hFH : G ∈ reducedFHGenus :=
    mem_reducedFHGenus_of_mem_reducedDetSeven_of_zeroCount G hred hcount
  have hrepG : G.Represents n := by
    apply (TernaryGram.represents_ofBasis_iff (tauLattice A) b n).2
    exact (represents_iff_exists_integralNorm A n).1 hrep
  rcases represents_of_reducedFHGenus G n hFH hrepG with hh | hf
  · exact Or.inr ((Irregular.hGram_represents_iff n).1 hh)
  · exact Or.inl ((Irregular.fGram_represents_iff n).1 hf)

/-- Given `SevenGramConstruction`, every `ResidualEligible` integer
is represented by `f` or `h`. -/
theorem eligible_f_or_h_of_gramConstruction
    (construction : SevenGramConstruction)
    (n : ℕ) (hn : Irregular.ResidualEligible n) :
    Irregular.RepresentsF (n : ℤ) ∨ Irregular.RepresentsH (n : ℤ) := by
  obtain ⟨data⟩ := construction n hn
  exact represents_f_or_h_of_positive_det_seven_zeroCount data.gram
    data.positive data.determinant data.zeroCount data.represents

end FibonacciCriterion.DeterminantSevenGenus
