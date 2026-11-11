import FibonacciCriterion.Forms.TernaryGram
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The Mordell construction

The definitions and algebra shared by the Mordell-type constructions for the
regular ternaries `⟨1,1,3⟩`, `⟨1,2,3⟩`, and `⟨1,2,5⟩`, after
Blackwell–Durham–Thompson–Treece. The manuscript cites Jones–Pall for the
sufficiency direction of these three criteria of Proposition 3.2; here that
direction is proven by the Mordell construction.

For an input `m` and a determinant `D`, the construction has five steps:

1. a table of cases fixes an integer `A` and an invertible residue class for an
   auxiliary prime, chosen so that the coefficient `a` (the prime or a fixed
   multiple of it) satisfies `m ∣ A² + a`, with `(A² + a)/m` in a prescribed
   residue class;
2. Dirichlet's theorem (`exists_auxiliary_prime`) gives a prime in that class;
3. quadratic reciprocity, applied in the files for each determinant, shows
   that the Legendre symbol needed at the auxiliary prime is 1, and a square
   root modulo that prime gives `h` and `b` with `ab - h² = Dm`
   (`exists_binary_unit_completion_of_legendre` at determinants 3 and 10,
   `ClassicalInputs.Regular123.SquareRoots` at determinant 6);
4. the coefficients form a `MordellDatum`, whose form has an integral symmetric
   Gram matrix, represents the input, has the prescribed determinant, and is
   positive definite (`MordellDatum.positive_of_determinant_pos`);
5. TauCeti's Minkowski reduction, a finite list of reduced Gram matrices, and a
   separating residue show that the target diagonal form represents the
   input.

The last section says how the files for each determinant carry out these
steps; one case at determinant 10 differs in steps 1 to 3. The Dirichlet and
square-root lemmas also serve the auxiliary-prime constructions of
Proposition 3.3 (`ClassicalInputs.DeterminantSeven.Unramified`,
`ClassicalInputs.DeterminantSeven.Ramified`). In the comments, `(a/m)` is the
Jacobi symbol, which is the Legendre symbol when `m` is prime.
-/

namespace FibonacciCriterion.MordellRegularity

/-! ## Auxiliary primes and square roots -/

/-- Dirichlet's theorem: for `q ≠ 0` and `r` prime to `q`, some prime
`p > N` satisfies `p ≡ r (mod q)`. -/
theorem exists_auxiliary_prime
    (N q r : ℕ) (hq : q ≠ 0) (hr : r.Coprime q) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p ≡ r [MOD q] :=
  Nat.forall_exists_prime_gt_and_modEq N hq hr

/-- For `q ≠ 0` and `r` prime to `q`, some prime has the form `r + qk` with
`k ≥ 0`. This form gives the Mordell quotients as integers rather than as
congruences. -/
theorem exists_auxiliary_prime_eq_add_mul
    (q r : ℕ) (hq : q ≠ 0) (hr : r.Coprime q) :
    ∃ p k : ℕ, p.Prime ∧ p = r + q * k := by
  obtain ⟨p, hrp, hp, hmod⟩ := exists_auxiliary_prime r q r hq hr
  have hdiv : q ∣ p - r :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hrp)).mp hmod.symm
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨p, k, hp, ?_⟩
  omega

/-- If `x ≡ r (mod q)` and `r` is prime to `q`, then `x` is prime to
`q`. -/
theorem coprime_of_modEq {x r q : ℕ} (hxr : x ≡ r [MOD q])
    (hr : r.Coprime q) : x.Coprime q := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hdx : x.gcd q ∣ x := Nat.gcd_dvd_left x q
  have hdq : x.gcd q ∣ q := Nat.gcd_dvd_right x q
  have hdr : x.gcd q ∣ r := (hxr.dvd_iff hdq).mp hdx
  exact Nat.eq_one_of_dvd_coprimes hr hdr hdq

/-- An invertible residue class modulo `modulus` whose members all satisfy
`P`: the conditions on an auxiliary prime, as one arithmetic progression. -/
structure PrimeProgression (P : ℕ → Prop) where
  /-- The modulus of the progression. -/
  modulus : ℕ
  /-- The residue of the progression modulo `modulus`. -/
  residue : ℕ
  modulus_ne_zero : modulus ≠ 0
  residue_coprime : residue.Coprime modulus
  forces : ∀ {p : ℕ}, p ≡ residue [MOD modulus] → P p

/-- The condition that `-a` is a square modulo `m`: some `A` in `ZMod m` has
`A² + a = 0`. -/
def HasNegSquareRoot (a m : ℕ) : Prop :=
  ∃ A : ZMod m, A ^ 2 + a = 0

/-- If `-a` is a square in `ZMod m`, then `HasNegSquareRoot a m`. -/
theorem hasNegSquareRoot_of_isSquare {a m : ℕ}
    (h : IsSquare (-(a : ZMod m))) : HasNegSquareRoot a m := by
  rcases h with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  rw [pow_two, ← hA]
  ring

/-- For a prime `p` not dividing `a`, the Legendre symbol `(-a/p) = 1` gives a
square root of `-a` modulo `p`. -/
theorem hasNegSquareRoot_of_legendreSym {a p : ℕ} [Fact p.Prime]
    (ha : ((-(a : ℤ)) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-(a : ℤ)) = 1) : HasNegSquareRoot a p := by
  apply hasNegSquareRoot_of_isSquare
  have ha' : (↑(-(a : ℤ)) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_neg] using ha
  simpa using (legendreSym.eq_one_iff p ha').mp hleg

/-- A square root of `-a` modulo `m` lifts to an integer `A` with
`m ∣ A² + a`. -/
theorem HasNegSquareRoot.exists_int_dvd {a m : ℕ} (h : HasNegSquareRoot a m) :
    ∃ A : ℤ, (m : ℤ) ∣ A ^ 2 + a := by
  rcases h with ⟨Amod, hAmod⟩
  rcases ZMod.intCast_surjective Amod with ⟨A, hA⟩
  refine ⟨A, (ZMod.intCast_zmod_eq_zero_iff_dvd (A ^ 2 + a) m).mp ?_⟩
  simpa [hA] using hAmod

/-- Binary completion: if `p ∤ d` and `(-d/p) = 1`, then `ps - dt² = 1` for
some integers `s, t`. The proof takes `t ≡ u/d (mod p)` with
`u² ≡ -d (mod p)`, so that `dt² ≡ -1 (mod p)`. -/
theorem exists_binary_unit_completion_of_legendre {d p : ℕ} [Fact p.Prime]
    (hd : ((d : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-(d : ℤ)) = 1) :
    ∃ s t : ℤ, (p : ℤ) * s - (d : ℤ) * t ^ 2 = 1 := by
  obtain ⟨u, hu⟩ := hasNegSquareRoot_of_legendreSym
    (by simpa only [Int.cast_neg] using (neg_ne_zero.mpr hd)) hleg
  have hd' : (d : ZMod p) ≠ 0 := by
    simpa only [Int.cast_natCast] using hd
  let v : ZMod p := u * ((d : ZMod p)⁻¹)
  have hu' : u ^ 2 = -(d : ZMod p) := by
    linear_combination hu
  have hv : (d : ZMod p) * v ^ 2 + 1 = 0 := by
    dsimp [v]
    rw [mul_pow, hu']
    field_simp [hd']
    ring
  obtain ⟨t, ht⟩ := ZMod.intCast_surjective v
  have hz : (((d : ℤ) * t ^ 2 + 1 : ℤ) : ZMod p) = 0 := by
    simpa [ht] using hv
  have hdiv : (p : ℤ) ∣ (d : ℤ) * t ^ 2 + 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  obtain ⟨s, hs⟩ := hdiv
  refine ⟨s, t, ?_⟩
  rw [← hs]
  ring

/-! ## The Mordell datum and its form -/

/-- Ternary forms, as integer-valued functions of three integers. The type
does not record the shape of the form; every form in this construction is a
polynomial with even cross terms, so it has an integral symmetric Gram
matrix. -/
abbrev TernaryForm := ℤ → ℤ → ℤ → ℤ

/-- `Q` represents `n`: `Q x y z = n` for some integers `x, y, z`. -/
def Represents (Q : TernaryForm) (n : ℤ) : Prop :=
  ∃ x y z : ℤ, Q x y z = n

/-- The data of the Mordell construction for the input `m` and determinant `D`:
integers `A, B, a, h, b` with `ab - h² = Dm`, together with the quotients
`cxx, cxy, cyy` of `A² + a`, `AB + h`, and `B² + b` by `m`. The quotients are
fields, so no integer division is needed. -/
structure MordellDatum (m D : ℤ) where
  /-- The coefficient `A` of `2xz` in the Mordell form, a square root of `-a`
  modulo `m`. -/
  A : ℤ
  /-- The coefficient `B` of `2yz` in the Mordell form, a square root of `-b`
  modulo `m`. -/
  B : ℤ
  /-- The coefficient `a` of `x²` in the binary form `ax² + 2hxy + by²` of
  determinant `Dm`. -/
  a : ℤ
  /-- The coefficient `h` of `2xy` in the binary form `ax² + 2hxy + by²`. -/
  h : ℤ
  /-- The coefficient `b` of `y²` in the binary form `ax² + 2hxy + by²`. -/
  b : ℤ
  /-- The quotient `(A² + a)/m`, the coefficient of `x²` in the Mordell
  form. -/
  cxx : ℤ
  /-- The quotient `(AB + h)/m`, the coefficient of `2xy` in the Mordell
  form. -/
  cxy : ℤ
  /-- The quotient `(B² + b)/m`, the coefficient of `y²` in the Mordell
  form. -/
  cyy : ℤ
  xx_eq : A ^ 2 + a = m * cxx
  xy_eq : A * B + h = m * cxy
  yy_eq : B ^ 2 + b = m * cyy
  determinant_eq : a * b - h ^ 2 = D * m

/-- The Mordell datum with `B = 0` and with `h` and `b` multiples of `m`. -/
def MordellDatum.ofBZero {m D A a h b cxx cxy cyy : ℤ}
    (hxx : A ^ 2 + a = m * cxx)
    (hxy : h = m * cxy)
    (hyy : b = m * cyy)
    (hdet : a * b - h ^ 2 = D * m) : MordellDatum m D where
  A := A
  B := 0
  a := a
  h := h
  b := b
  cxx := cxx
  cxy := cxy
  cyy := cyy
  xx_eq := hxx
  xy_eq := by simpa using hxy
  yy_eq := by simpa using hyy
  determinant_eq := hdet

/-- The Mordell form
`cxx x² + 2 cxy xy + cyy y² + 2A xz + 2B yz + m z²` of a datum. -/
def MordellDatum.form {m D : ℤ} (d : MordellDatum m D) : TernaryForm :=
  fun x y z ↦
    d.cxx * x ^ 2 + 2 * d.cxy * x * y + d.cyy * y ^ 2 +
      2 * d.A * x * z + 2 * d.B * y * z + m * z ^ 2

/-- The numerator identity
`m Q(x, y, z) = (Ax + By + mz)² + (ax² + 2hxy + by²)`, on which the
construction rests. -/
theorem MordellDatum.mul_form {m D : ℤ} (d : MordellDatum m D) (x y z : ℤ) :
    m * d.form x y z =
      (d.A * x + d.B * y + m * z) ^ 2 +
        (d.a * x ^ 2 + 2 * d.h * x * y + d.b * y ^ 2) := by
  calc
    m * d.form x y z =
        (m * d.cxx) * x ^ 2 + 2 * (m * d.cxy) * x * y +
          (m * d.cyy) * y ^ 2 + 2 * m * d.A * x * z +
          2 * m * d.B * y * z + m ^ 2 * z ^ 2 := by
      rw [MordellDatum.form]
      ring
    _ = (d.A * x + d.B * y + m * z) ^ 2 +
          (d.a * x ^ 2 + 2 * d.h * x * y + d.b * y ^ 2) := by
      rw [← d.xx_eq, ← d.xy_eq, ← d.yy_eq]
      ring

/-- The Mordell form represents its input `m`, at `(0, 0, 1)`. -/
theorem MordellDatum.represents_input {m D : ℤ} (d : MordellDatum m D) :
    Represents d.form m := by
  refine ⟨0, 0, 1, ?_⟩
  simp [MordellDatum.form]

/-- The Mordell form represents its leading coefficient `cxx = (A² + a)/m`,
at `(1, 0, 0)`. This value is the separator that singles out the target
class. -/
theorem MordellDatum.represents_cxx {m D : ℤ} (d : MordellDatum m D) :
    Represents d.form d.cxx := by
  refine ⟨1, 0, 0, ?_⟩
  simp [MordellDatum.form]

/-- The determinant of the symmetric Gram matrix
`[[cxx,cxy,A],[cxy,cyy,B],[A,B,m]]`. -/
def MordellDatum.gramDet {m D : ℤ} (d : MordellDatum m D) : ℤ :=
  d.cxx * d.cyy * m + 2 * d.cxy * d.A * d.B -
    d.cxx * d.B ^ 2 - d.cyy * d.A ^ 2 - m * d.cxy ^ 2

/-- For `m ≠ 0`, the Mordell form has determinant `D`. -/
theorem MordellDatum.gramDet_eq {m D : ℤ} (d : MordellDatum m D) (hm : m ≠ 0) :
    d.gramDet = D := by
  apply mul_left_cancel₀ hm
  calc
    m * d.gramDet =
        (m * d.cxx) * (m * d.cyy) + 2 * (m * d.cxy) * d.A * d.B -
          (m * d.cxx) * d.B ^ 2 - (m * d.cyy) * d.A ^ 2 - (m * d.cxy) ^ 2 := by
      rw [MordellDatum.gramDet]
      ring
    _ = d.a * d.b - d.h ^ 2 := by
      rw [← d.xx_eq, ← d.xy_eq, ← d.yy_eq]
      ring
    _ = D * m := d.determinant_eq
    _ = m * D := by ring

/-- The integral symmetric Gram matrix of a Mordell datum. -/
def MordellDatum.ternaryGram {m D : ℤ} (d : MordellDatum m D) : TernaryGram :=
  ⟨d.cxx, d.cyy, m, d.cxy, d.A, d.B⟩

/-- The form of `d.ternaryGram` is `d.form`. -/
theorem MordellDatum.ternaryGram_eval {m D : ℤ} (d : MordellDatum m D)
    (x y z : ℤ) : d.ternaryGram.eval x y z = d.form x y z := by
  simp only [MordellDatum.ternaryGram, TernaryGram.eval, MordellDatum.form]
  ring

/-- For `m ≠ 0`, `d.ternaryGram` has determinant `D`. -/
theorem MordellDatum.ternaryGram_det {m D : ℤ} (d : MordellDatum m D)
    (hm : m ≠ 0) : d.ternaryGram.det = D := by
  change d.gramDet = D
  exact d.gramDet_eq hm

/-- `d.ternaryGram` and `d.form` represent the same integers. -/
theorem MordellDatum.ternaryGram_represents_iff {m D : ℤ}
    (d : MordellDatum m D) (n : ℤ) :
    d.ternaryGram.Represents n ↔ Represents d.form n := by
  simp only [TernaryGram.Represents, Represents, d.ternaryGram_eval]

/-- Positive definiteness of a ternary form: it is positive at every nonzero
integer vector. -/
def PositiveTernary (Q : TernaryForm) : Prop :=
  ∀ x y z : ℤ, x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 → 0 < Q x y z

/-- If `m > 0`, `D > 0`, and `a > 0`, the Mordell form is positive
definite. The binary form `ax² + 2hxy + by²` has determinant `Dm > 0`. -/
theorem MordellDatum.positive_of_determinant_pos {m D : ℤ} (hm : 0 < m)
    (d : MordellDatum m D) (hD : 0 < D) (ha : 0 < d.a) : PositiveTernary d.form := by
  intro x y z hne
  by_cases hxy : x = 0 ∧ y = 0
  · rcases hxy with ⟨rfl, rfl⟩
    have hz : z ≠ 0 := by tauto
    have hzsq : 0 < z ^ 2 := sq_pos_of_ne_zero hz
    simp only [MordellDatum.form, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, zero_mul, zero_add]
    exact mul_pos hm hzsq
  · have hbin :
        0 < d.a * x ^ 2 + 2 * d.h * x * y + d.b * y ^ 2 := by
      by_cases hy : y = 0
      · subst y
        have hx : x ≠ 0 := by tauto
        have hxsq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
        simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
          add_zero]
        exact mul_pos ha hxsq
      · have hysq : 0 < y ^ 2 := sq_pos_of_ne_zero hy
        have hdet := d.determinant_eq
        have hid :
            d.a * (d.a * x ^ 2 + 2 * d.h * x * y + d.b * y ^ 2) =
              (d.a * x + d.h * y) ^ 2 +
                (d.a * d.b - d.h ^ 2) * y ^ 2 := by ring
        rw [hdet] at hid
        have hrhs :
            0 < (d.a * x + d.h * y) ^ 2 + (D * m) * y ^ 2 := by
          exact add_pos_of_nonneg_of_pos (sq_nonneg _)
            (mul_pos (mul_pos hD hm) hysq)
        have hprod :
            0 < d.a * (d.a * x ^ 2 + 2 * d.h * x * y + d.b * y ^ 2) := by
          rw [hid]
          exact hrhs
        rcases (mul_pos_iff.mp hprod) with hgood | hbad
        · exact hgood.2
        · exact (not_lt_of_ge ha.le hbad.1).elim
    have hmul := d.mul_form x y z
    have hrhs :
        0 < (d.A * x + d.B * y + m * z) ^ 2 +
          (d.a * x ^ 2 + 2 * d.h * x * y + d.b * y ^ 2) :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) hbin
    have hprod : 0 < m * d.form x y z := by
      rw [hmul]
      exact hrhs
    rcases (mul_pos_iff.mp hprod) with hgood | hbad
    · exact hgood.2
    · exact (not_lt_of_ge hm.le hbad.1).elim

/-! ## Jacobi symbols -/

/-- If `p ≡ r (mod m)` and `d + r = mc`, then `(p/m) = (-d/m)` as Jacobi
symbols. The reciprocity arguments at determinants 3 and 7 use this. -/
theorem jacobi_of_separator_residue {p r d m c : ℕ}
    (hpr : p ≡ r [MOD m]) (hid : d + r = m * c) :
    jacobiSym (p : ℤ) m = jacobiSym (-(d : ℤ)) m := by
  have hr : (r : ℤ) ≡ -(d : ℤ) [ZMOD (m : ℤ)] := by
    apply Int.modEq_iff_add_fac.mpr
    refine ⟨-(c : ℤ), ?_⟩
    have hz : (d : ℤ) + (r : ℤ) = (m : ℤ) * (c : ℤ) := by
      exact_mod_cast hid
    linear_combination -hz
  exact jacobiSym.mod_left' ((Int.natCast_modEq_iff.mpr hpr).trans hr)

/-- For odd `m`, `(-3/m) = (m/3)` as Jacobi symbols. Here `m` may be
composite, so the input of the Mordell construction need not be factored. -/
theorem jacobi_neg_three_swap {m : ℕ} (hm : Odd m) :
    jacobiSym (-3) m = jacobiSym (m : ℤ) 3 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with hm4 | hm4
  · rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num,
      jacobiSym.neg _ hm, ZMod.χ₄_nat_one_mod_four hm4,
      jacobiSym.quadratic_reciprocity_one_mod_four'
        (by decide : Odd (3 : ℕ)) hm4, one_mul]
  · rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num,
      jacobiSym.neg _ hm, ZMod.χ₄_nat_three_mod_four hm4,
      jacobiSym.quadratic_reciprocity_three_mod_four
        (by norm_num : (3 : ℕ) % 4 = 3) hm4]
    ring

/-! ## The target forms

This section defines the forms `⟨1,1,3⟩` and `⟨1,2,3⟩`. The files for each
determinant carry out the construction and prove the classifications at
determinants 3, 6, and 10; the obstruction files prove necessity.
-/

/-- The diagonal form `⟨1,1,3⟩`, that is `x² + y² + 3z²`. -/
def Q113 : TernaryForm := fun x y z ↦ x ^ 2 + y ^ 2 + 3 * z ^ 2
/-- The diagonal form `⟨1,2,3⟩`, that is `x² + 2y² + 3z²`. -/
def Q123 : TernaryForm := fun x y z ↦ x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2

/-! ## Use in the files for each determinant

The files for each determinant use this construction as follows.

* **Prime classes:** each row of the case tables gives one residue class,
  prime to its modulus, that forces every required Legendre symbol value. At
  determinant 3 the class combines two congruence conditions by the Chinese
  remainder theorem; at determinants 6 and 10 it is written out.
* **Roots:** the coefficient `A` is a fixed integer taken from the row. The
  coefficient `a` is the auxiliary prime or a fixed multiple of it (`3p`,
  `2p`, `4q`), and the prime is chosen in a progression that makes
  `m ∣ A² + a` with the prescribed separator residue of `(A² + a)/m`; no
  square root modulo `m` is extracted and `m` is not factored. (For `⟨1,2,5⟩`
  with `m = 2n`, `n ≡ 3 (mod 4)`, the auxiliary prime is `b`, or `b/5` when
  `5 ∣ n`, and `A` comes from a square root modulo that prime.)
* **Binary completion:** `h` and `b` are chosen with `ab - h² = Dm` and the
  divisibility required by `MordellDatum`, and the form is shown to be positive.
* **Finite classification:** TauCeti reduction at determinants 3, 6, and 10,
  with the lists of reduced integral Gram matrices, shows that the separators
  (a value `≡ 5 (mod 8)`; an odd value `≡ 3 (mod 9)`; a value `≡ 6 (mod 16)`
  together with an odd value) exclude every class except that of the target.
* **Transport:** representations are carried along the explicit unimodular
  equivalences to the representation predicates of the target forms.

No local-global principle (Hasse–Minkowski) is used.
-/

end FibonacciCriterion.MordellRegularity
