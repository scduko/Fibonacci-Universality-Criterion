import FibonacciCriterion.ClassicalInputs.ThreeSquares.Obstruction
import FibonacciCriterion.ClassicalInputs.Regular125.Obstruction
import FibonacciCriterion.ClassicalInputs.Mordell
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Sufficiency for `⟨1,2,5⟩`: the Mordell construction

The manuscript cites Jones–Pall for the `⟨1,2,5⟩` row of Proposition 3.2; here
its sufficiency direction is proven by the Mordell-type construction of
Blackwell–Durham–Thompson–Treece. Dirichlet's theorem and quadratic
reciprocity give a Mordell datum of determinant 10 for every positive
nonexceptional integer divisible by neither 4 nor 25
(`NormalizedParameterConstruction`). The statement that the Mordell form of
such a datum represents the same integers as one of four forms of determinant
10, one of them even-valued, is the hypothesis
`DeterminantTenClassification`; `ClassicalInputs.Regular125.Classification`
proves it from the list of reduced matrices. The main theorem is
`regular125Sufficiency_of_classification`.

The classes `RepresentsQ2` and `RepresentsQ3` represent no integer
`≡ 6 (mod 16)`, and the even-valued class `RepresentsQ4` represents no odd
integer. The Mordell form is therefore required to have leading coefficient
`≡ 6 (mod 16)` and to represent an odd integer. For odd `m` the input is the
odd value. For even `m`, a datum with `B = 0`, odd `a`, and such a leading
coefficient has no odd value (see `NormalizedParameterConstruction`), so even
inputs `m = 2n` use `a = 4q` for `n ≡ 1 (mod 4)`, and `B = 1` or `B = 5` for
`n ≡ 3 (mod 4)`. Descent by 4 and 25 extends the result from the normalized
inputs to every nonnegative integer outside the exceptional set.
-/

namespace FibonacciCriterion

open ClassicalRepresentation

namespace Mordell125

/-! ## The four determinant-10 classes and their separators -/

/-- Representation by `2x² + 2y² + 2xz + 3z²`. -/
def RepresentsQ2 (n : ℤ) : Prop :=
  ∃ x y z : ℤ, 2 * x ^ 2 + 2 * y ^ 2 + 2 * x * z + 3 * z ^ 2 = n

/-- Representation by `x² + y² + 10z²`. -/
def RepresentsQ3 (n : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 10 * z ^ 2 = n

/-- Representation by `2x² + 2y² + 4z² - 2xy - 2xz`, the even-valued fourth
class of determinant 10. Lists of forms whose polynomial coefficients have
gcd 1 omit this class, but it is a class of integral symmetric Gram
matrices. -/
def RepresentsQ4 (n : ℤ) : Prop :=
  ∃ x y z : ℤ,
    2 * x ^ 2 + 2 * y ^ 2 + 4 * z ^ 2 - 2 * x * y - 2 * x * z = n

/-- The form `x² + y² + 10z²` represents no integer `≡ 6 (mod 16)`. -/
theorem q3_not_six_mod_sixteen (n : ℤ) (hn : n % 16 = 6) :
    ¬ RepresentsQ3 n := by
  rintro ⟨x, y, z, rfl⟩
  rcases RegularReductions.square_mod_sixteen x with hx | hx | hx | hx <;>
    rcases RegularReductions.square_mod_sixteen y with hy | hy | hy | hy <;>
      rcases RegularReductions.square_mod_sixteen z with hz | hz | hz | hz <;>
        norm_num [Int.add_emod, Int.mul_emod, hx, hy, hz] at hn

/-- The form `2x² + 2y² + 2xz + 3z²` represents no integer `≡ 6 (mod 16)`.

Parity forces `z = 2w`; completing the square and halving the congruence
reduces the claim to the squares 0, 1, 4 modulo 8.
-/
theorem q2_not_six_mod_sixteen (n : ℤ) (hn : n % 16 = 6) :
    ¬ RepresentsQ2 n := by
  rintro ⟨x, y, z, rfl⟩
  have hz : z % 2 = 0 := by
    have hpar := congrArg (fun t : ℤ ↦ t % 2) hn
    have hzlo : 0 ≤ z % 2 := Int.emod_nonneg _ (by norm_num)
    have hzhi : z % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
    generalize hzr : z % 2 = zr at hzlo hzhi hpar ⊢
    interval_cases zr
    · rfl
    · norm_num [pow_two, Int.add_emod, Int.mul_emod, hzr] at hpar
  obtain ⟨w, hw⟩ := Int.dvd_iff_emod_eq_zero.mpr hz
  have hid :
      2 * x ^ 2 + 2 * y ^ 2 + 2 * x * z + 3 * z ^ 2 =
        2 * ((x + w) ^ 2 + y ^ 2 + 5 * w ^ 2) := by
    rw [hw]
    ring
  rw [hid] at hn
  have hmod16 : Int.ModEq 16
      (2 * ((x + w) ^ 2 + y ^ 2 + 5 * w ^ 2)) 6 := hn
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod16
  have hmod8 : Int.ModEq 8 ((x + w) ^ 2 + y ^ 2 + 5 * w ^ 2) 3 := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨k, by nlinarith⟩
  change ((x + w) ^ 2 + y ^ 2 + 5 * w ^ 2) % 8 = 3 at hmod8
  rcases RegularReductions.square_mod_eight (x + w) with ha | ha | ha <;>
    rcases RegularReductions.square_mod_eight y with hy | hy | hy <;>
      rcases RegularReductions.square_mod_eight w with hw | hw | hw <;>
        norm_num [Int.add_emod, Int.mul_emod, ha, hy, hw] at hmod8

/-- The fourth class of determinant 10 represents only even integers. -/
theorem q4_even {n : ℤ} (hn : RepresentsQ4 n) : n % 2 = 0 := by
  rcases hn with ⟨x, y, z, rfl⟩
  norm_num [Int.add_emod, Int.sub_emod, Int.mul_emod]

/-! ## The Mordell datum at determinant 10 -/

/-- A Mordell datum of determinant 10 for the input `m`. -/
abbrev Datum (m : ℤ) := MordellRegularity.MordellDatum m 10

/-- The Mordell form of `d` represents `n`. This is
`MordellRegularity.Represents d.form n`, so `MordellDatum.represents_input` and
`MordellDatum.represents_cxx` apply. -/
def Datum.Represents {m : ℤ} (d : Datum m) (n : ℤ) : Prop :=
  MordellRegularity.Represents d.form n

/-- The Mordell form of `d` represents an odd integer. This excludes the
even-valued class `RepresentsQ4`. -/
def Datum.HasOddValue {m : ℤ} (d : Datum m) : Prop :=
  ∃ n : ℤ, d.Represents n ∧ n % 2 = 1

/-- The Mordell form represents its second diagonal coefficient `cyy`. -/
theorem Datum.represents_cyy {m : ℤ} (d : Datum m) : d.Represents d.cyy := by
  exact ⟨0, 1, 0, by simp [MordellRegularity.MordellDatum.form]⟩

/-! ## Even inputs: the datum with `a = 4q`

After powers of 4 are removed, an even input is `m = 2n` with `n` odd. Since
the leading coefficient `E` is even, an even `a` with `A² + a = 2nE` has `A`
even and is divisible by 4; write `a = 4q`. The
hypotheses of `evenDatum` are the root equation and the binary completion
equation. -/

/-- The Mordell datum for the even input `2n` with `A = 2u`, `B = 0`,
`a = 4q`, `h = 2nk`, and `b = 2nc`, given the root equation
`2(u² + q) = nE` and the completion equation `2qc - nk² = 5`. -/
def evenDatum (n q u k c E : ℤ)
    (hlead : 2 * (u ^ 2 + q) = n * E)
    (hdet : 2 * q * c - n * k ^ 2 = 5) : Datum (2 * n) where
  A := 2 * u
  B := 0
  a := 4 * q
  h := 2 * n * k
  b := 2 * n * c
  cxx := E
  cxy := k
  cyy := c
  xx_eq := by nlinarith
  xy_eq := by ring
  yy_eq := by ring
  determinant_eq := by
    calc
      4 * q * (2 * n * c) - (2 * n * k) ^ 2 =
          4 * n * (2 * q * c - n * k ^ 2) := by ring
      _ = 4 * n * 5 := by rw [hdet]
      _ = 10 * (2 * n) := by ring

/-- If `q > 0`, `E ≡ 6 (mod 16)`, and `c` is odd, then `evenDatum` meets the
three conditions of `NormalizedParameterConstruction`: `a > 0`,
`cxx ≡ 6 (mod 16)`, and an odd represented value (`c`).
-/
theorem evenDatum_conditions (n q u k c E : ℤ)
    (hlead : 2 * (u ^ 2 + q) = n * E)
    (hdet : 2 * q * c - n * k ^ 2 = 5)
    (hq : 0 < q) (hE : E % 16 = 6) (hc : c % 2 = 1) :
    0 < (evenDatum n q u k c E hlead hdet).a ∧
      (evenDatum n q u k c E hlead hdet).cxx % 16 = 6 ∧
      (evenDatum n q u k c E hlead hdet).HasOddValue := by
  refine ⟨by simp [evenDatum]; omega, by simpa [evenDatum], ?_⟩
  refine ⟨c, (evenDatum n q u k c E hlead hdet).represents_cyy, hc⟩

/-! A second construction for even inputs allows `B ≠ 0`. Set

`b = 2nc - B²`, `h = 2nk - AB`, and `a = 2nE - A²`.

After multiplication by the second diagonal coefficient `c`, the determinant
condition becomes

`b(Ec - k²) - (cA - kB)² = 10c`.

This construction serves the residue classes in which the `B = 0`
construction with `q` and `c` odd is obstructed modulo 4. -/

/-- The Mordell datum for the even input `2n` with arbitrary `B` and second
diagonal coefficient `c ≠ 0`: `a = 2nE - A²`, `h = 2nk - AB`, and
`b = 2nc - B²`, given `b(Ec - k²) - (cA - kB)² = 10c`. -/
def oddBDatum (n B c b E k A : ℤ)
    (hb : b = 2 * n * c - B ^ 2)
    (hcore : b * (E * c - k ^ 2) - (c * A - k * B) ^ 2 = 10 * c)
    (hc : c ≠ 0) : Datum (2 * n) where
  A := A
  B := B
  a := 2 * n * E - A ^ 2
  h := 2 * n * k - A * B
  b := b
  cxx := E
  cxy := k
  cyy := c
  xx_eq := by ring
  xy_eq := by ring
  yy_eq := by rw [hb]; ring
  determinant_eq := by
    apply mul_left_cancel₀ hc
    calc
      c * ((2 * n * E - A ^ 2) * b - (2 * n * k - A * B) ^ 2) =
          2 * n * (b * (E * c - k ^ 2) - (c * A - k * B) ^ 2) := by
            rw [hb]
            ring
      _ = 2 * n * (10 * c) := by rw [hcore]
      _ = c * (10 * (2 * n)) := by ring

/-- If `n > 0` and `b > 0`, then `a > 0`. With `E ≡ 6 (mod 16)` and `c` odd,
`oddBDatum` meets the conditions of `NormalizedParameterConstruction`. -/
theorem oddBDatum_conditions (n B c b E k A : ℤ)
    (hb : b = 2 * n * c - B ^ 2)
    (hcore : b * (E * c - k ^ 2) - (c * A - k * B) ^ 2 = 10 * c)
    (hc0 : c ≠ 0) (hn : 0 < n) (hbpos : 0 < b)
    (hE : E % 16 = 6) (hcodd : c % 2 = 1) :
    0 < (oddBDatum n B c b E k A hb hcore hc0).a ∧
      (oddBDatum n B c b E k A hb hcore hc0).cxx % 16 = 6 ∧
      (oddBDatum n B c b E k A hb hcore hc0).HasOddValue := by
  let d := oddBDatum n B c b E k A hb hcore hc0
  have hprod : 0 < d.a * b := by
    have hsq : 0 ≤ d.h ^ 2 := sq_nonneg d.h
    have hdet := d.determinant_eq
    have hdb : d.b = b := rfl
    rw [hdb] at hdet
    nlinarith
  have ha : 0 < d.a := by
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.1
    · omega
  refine ⟨ha, by simpa [d, oddBDatum] using hE, ?_⟩
  refine ⟨c, d.represents_cyy, hcodd⟩

/-- The case `B = 1` of `oddBDatum`, used when `n ≡ 3 (mod 4)` and `5 ∤ n`.
Here `b = p = 2nc - 1`, `L = cA - k` is a square root of `-10c` modulo `p`,
and `r = Ec - k²` is the quotient `(L² + 10c)/p`. In the application `p` is a
prime with `p ≡ 2n - 1 (mod 32n)` and `p ≡ 2 (mod 5)`, a nonsquare modulo
5; then `c = (p + 1)/(2n) ≡ 1 (mod 16)`, and reciprocity gives the square
root of `-10c` modulo `p`. -/
def oddBOneDatum (n c p L r k E A : ℤ)
    (hp : p = 2 * n * c - 1)
    (hr : p * r - L ^ 2 = 10 * c)
    (hL : L = c * A - k)
    (hrE : r = E * c - k ^ 2)
    (hc : c ≠ 0) : Datum (2 * n) :=
  oddBDatum n 1 c p E k A (by simpa using hp)
    (by simpa [hL, hrE] using hr) hc

/-- If `n > 0`, `p > 0`, `E ≡ 6 (mod 16)`, and `c` is odd, then
`oddBOneDatum` meets the conditions of `NormalizedParameterConstruction`. -/
theorem oddBOneDatum_conditions (n c p L r k E A : ℤ)
    (hp : p = 2 * n * c - 1)
    (hr : p * r - L ^ 2 = 10 * c)
    (hL : L = c * A - k)
    (hrE : r = E * c - k ^ 2)
    (hc0 : c ≠ 0) (hn : 0 < n) (hppos : 0 < p)
    (hE : E % 16 = 6) (hcodd : c % 2 = 1) :
    0 < (oddBOneDatum n c p L r k E A hp hr hL hrE hc0).a ∧
      (oddBOneDatum n c p L r k E A hp hr hL hrE hc0).cxx % 16 = 6 ∧
      (oddBOneDatum n c p L r k E A hp hr hL hrE hc0).HasOddValue := by
  exact oddBDatum_conditions n 1 c p E k A (by simpa using hp)
    (by simpa [hL, hrE] using hr) hc0 hn hppos hE hcodd

/-- The completion equation of `oddBDatum` for `B = 5`, from the reduced
equation `Pr - 5d² = 2c`. -/
theorem bFive_completion {c P d r k E v : ℤ}
    (hr : P * r - 5 * d ^ 2 = 2 * c) (hd : d = c * v - k) (hrE : r = E * c - k ^ 2) :
    5 * P * (E * c - k ^ 2) - (c * (5 * v) - k * 5) ^ 2 = 10 * c := by
  calc
    5 * P * (E * c - k ^ 2) - (c * (5 * v) - k * 5) ^ 2 =
        5 * (P * (E * c - k ^ 2) - 5 * (c * v - k) ^ 2) := by ring
    _ = 5 * (P * r - 5 * d ^ 2) := by rw [hrE, hd]
    _ = 5 * (2 * c) := by rw [hr]
    _ = 10 * c := by ring

/-- The case `B = 5` of `oddBDatum`, used when `n = 5s` with
`s ≡ 3 (mod 4)`. Writing `b = 5P` removes the forced factor 5; the reduced
completion equation is `Pr - 5d² = 2c`. In the application
`P ≡ 2s - 5 (mod 32s)`, so `c = (P + 5)/(2s) ≡ 1 (mod 16)`, and the root
condition depends on the Legendre symbol `(-s/P)`. -/
def oddBFiveDatum (s c P d r k E v : ℤ)
    (hP : P = 2 * s * c - 5)
    (hr : P * r - 5 * d ^ 2 = 2 * c)
    (hd : d = c * v - k)
    (hrE : r = E * c - k ^ 2)
    (hc : c ≠ 0) : Datum (2 * (5 * s)) :=
  oddBDatum (5 * s) 5 c (5 * P) E k (5 * v)
    (by rw [hP]; ring)
    (bFive_completion hr hd hrE)
    hc

/-- If `s > 0`, `P > 0`, `E ≡ 6 (mod 16)`, and `c` is odd, then
`oddBFiveDatum` meets the conditions of `NormalizedParameterConstruction`. -/
theorem oddBFiveDatum_conditions (s c P d r k E v : ℤ)
    (hP : P = 2 * s * c - 5)
    (hr : P * r - 5 * d ^ 2 = 2 * c)
    (hd : d = c * v - k)
    (hrE : r = E * c - k ^ 2)
    (hc0 : c ≠ 0) (hs : 0 < s) (hPpos : 0 < P)
    (hE : E % 16 = 6) (hcodd : c % 2 = 1) :
    0 < (oddBFiveDatum s c P d r k E v hP hr hd hrE hc0).a ∧
      (oddBFiveDatum s c P d r k E v hP hr hd hrE hc0).cxx % 16 = 6 ∧
      (oddBFiveDatum s c P d r k E v hP hr hd hrE hc0).HasOddValue := by
  exact oddBDatum_conditions (5 * s) 5 c (5 * P) E k (5 * v)
    (by rw [hP]; ring)
    (bFive_completion hr hd hrE)
    hc0 (by positivity) (by positivity) hE hcodd

/-! ## The classification and parameter statements -/

/-- The classification at determinant 10: if `m > 0` and `a > 0`, the
Mordell form of a datum of determinant 10 represents the same integers as
`⟨1,2,5⟩`, `RepresentsQ2`, `RepresentsQ3`, or `RepresentsQ4`. The positivity
hypotheses are those the Mordell construction supplies.
`ClassicalInputs.Regular125.Classification` proves this statement.
-/
def DeterminantTenClassification : Prop :=
  ∀ {m : ℤ} (d : Datum m), 0 < m → 0 < d.a →
    ((∀ n : ℤ, d.Represents n ↔ Represents125 n) ∨
      (∀ n : ℤ, d.Represents n ↔ RepresentsQ2 n) ∨
      (∀ n : ℤ, d.Represents n ↔ RepresentsQ3 n) ∨
      (∀ n : ℤ, d.Represents n ↔ RepresentsQ4 n))

/-- The parameter construction for normalized inputs: every positive
nonexceptional `m` divisible by neither 4 nor 25 has a Mordell datum of
determinant 10 with `a > 0`, `cxx ≡ 6 (mod 16)`, and an odd value.

The odd value matters when `m` is even. A datum with `B = 0`, odd `a`, and
`cxx ≡ 6 (mod 16)` then has none: `h = m·cxy`, `b = m·cyy`, and
`a·cyy - m·cxy² = 10`, so `cyy` is even, and the diagonal coefficients `cxx`,
`cyy`, `m` are all even. For example, at `m = 2` the choices `a = 3`, `A = 3`,
`h = 20`, `b = 140`, `B = 0` give the Gram matrix

`[[6,10,3],[10,70,0],[3,0,2]]`,

which satisfies the Mordell equations and has determinant 10 but represents
only even integers; it therefore represents the same integers as the fourth
class above, not as `⟨1,2,5⟩`. (The example is a hand computation, not a Lean
declaration.) For `m = 2n` with `n ≡ 1 (mod 4)`, the construction here takes
`a = 4q` with `q` and `cyy` odd (`evenDatum`); this choice is obstructed modulo
4 when `n ≡ 3 (mod 4)`, where `B = 1` or `B = 5` is used instead
(`oddBDatum`).

The statement is proven by
`normalizedParameterConstruction_of_two_arithmetic_inputs` from
`oddParameterArithmetic` and `evenOneModFourArithmetic`. -/
def NormalizedParameterConstruction : Prop :=
  ∀ m : ℤ, 0 < m → ¬ (25 : ℤ) ∣ m → ¬ (4 : ℤ) ∣ m →
    ¬ Exceptional125 m →
    ∃ d : Datum m, 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue

/-! The parameter construction splits into four cases: odd `m`, and
`m = 2n` with `n ≡ 1 (mod 4)`, with `n ≡ 3 (mod 4)` and `5 ∤ n`, or with
`n ≡ 3 (mod 4)` and `5 ∣ n`. Odd inputs use `oddInputDatum`; the case
`n ≡ 1 (mod 4)` uses `evenUnitFiveDatum` or `evenFiveDatum`; the two cases
`n ≡ 3 (mod 4)` use `oddBOneDatum` and `oddBFiveDatum`. -/

/-- The odd case of the parameter construction: the statement of
`NormalizedParameterConstruction` for odd `m`. -/
def OddParameterArithmetic : Prop :=
  ∀ m : ℤ, 0 < m → ¬ (25 : ℤ) ∣ m → ¬ (4 : ℤ) ∣ m →
    ¬ Exceptional125 m → ¬ (2 : ℤ) ∣ m →
    ∃ d : Datum m, 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue

/-- The case `n ≡ 1 (mod 4)` of the parameter construction: the statement of
`NormalizedParameterConstruction` for `m = 2n` with `n ≡ 1 (mod 4)`. -/
def EvenOneModFourArithmetic : Prop :=
  ∀ n : ℤ, 0 < n → ¬ (25 : ℤ) ∣ 2 * n → ¬ (4 : ℤ) ∣ 2 * n →
    ¬ Exceptional125 (2 * n) → n % 4 = 1 →
    ∃ d : Datum (2 * n), 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue

/-- The case `n ≡ 3 (mod 4)`, `5 ∤ n` of the parameter construction: the
statement of `NormalizedParameterConstruction` for `m = 2n` with
`n ≡ 3 (mod 4)` and `5 ∤ n`. -/
def EvenThreeModFourUnitArithmetic : Prop :=
  ∀ n : ℤ, 0 < n → ¬ (25 : ℤ) ∣ 2 * n → ¬ (4 : ℤ) ∣ 2 * n →
    ¬ Exceptional125 (2 * n) → n % 4 = 3 → ¬ (5 : ℤ) ∣ n →
    ∃ d : Datum (2 * n), 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue

/-- The case `n ≡ 3 (mod 4)`, `5 ∣ n` of the parameter construction: the
statement of `NormalizedParameterConstruction` for `m = 2n` with
`n ≡ 3 (mod 4)` and `5 ∣ n`. -/
def EvenThreeModFourFiveArithmetic : Prop :=
  ∀ n : ℤ, 0 < n → ¬ (25 : ℤ) ∣ 2 * n → ¬ (4 : ℤ) ∣ 2 * n →
    ¬ Exceptional125 (2 * n) → n % 4 = 3 → (5 : ℤ) ∣ n →
    ∃ d : Datum (2 * n), 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue

/-! ## Even inputs with `n ≡ 3 (mod 4)`: the cases `B = 1` and `B = 5` -/

/-- The arithmetic data for the case `B = 1`: integers with
`p = 2nc - 1 > 0`, `pr - L² = 10c`, `L = cA - k`, `r = Ec - k²`,
`E ≡ 6 (mod 16)`, and `c` odd. These are the hypotheses of
`oddBOneDatum_conditions`. -/
structure BOneRootData (n : ℤ) where
  /-- The second diagonal coefficient `c = (p + 1)/(2n)` of the Mordell
  form. -/
  c : ℤ
  /-- The coefficient `b = p = 2nc - 1` of the Mordell datum. In the
  application `p` is the auxiliary prime. -/
  p : ℤ
  /-- The square root `L = cA - k` of `-10c` modulo `p`. -/
  L : ℤ
  /-- The quotient `r = (L² + 10c)/p`, equal to `Ec - k²`. -/
  r : ℤ
  /-- The coefficient `k` of `2xy` in the Mordell form. -/
  k : ℤ
  /-- The leading coefficient `E` of the Mordell form. -/
  E : ℤ
  /-- The coefficient `A` of `2xz` in the Mordell form. -/
  A : ℤ
  p_eq : p = 2 * n * c - 1
  root_eq : p * r - L ^ 2 = 10 * c
  L_eq : L = c * A - k
  r_eq : r = E * c - k ^ 2
  c_ne : c ≠ 0
  p_pos : 0 < p
  E_mod : E % 16 = 6
  c_odd : c % 2 = 1

/-- The arithmetic data for the case `B = 5`, where `n = 5s`: integers with
`P = 2sc - 5 > 0`, `Pr - 5d² = 2c`, `d = cv - k`, `r = Ec - k²`,
`E ≡ 6 (mod 16)`, and `c` odd. -/
structure BFiveRootData (s : ℤ) where
  /-- The second diagonal coefficient `c = (P + 5)/(2s)` of the Mordell
  form. -/
  c : ℤ
  /-- The integer `P = 2sc - 5`; the Mordell datum has `b = 5P`. In the
  application `P` is the auxiliary prime. -/
  P : ℤ
  /-- The root `d = cv - k` of `5d² ≡ -2c (mod P)`. -/
  d : ℤ
  /-- The quotient `r = (5d² + 2c)/P`, equal to `Ec - k²`. -/
  r : ℤ
  /-- The coefficient `k` of `2xy` in the Mordell form. -/
  k : ℤ
  /-- The leading coefficient `E` of the Mordell form. -/
  E : ℤ
  /-- The integer `v`; the coefficient of `2xz` in the Mordell form is
  `A = 5v`. -/
  v : ℤ
  P_eq : P = 2 * s * c - 5
  root_eq : P * r - 5 * d ^ 2 = 2 * c
  d_eq : d = c * v - k
  r_eq : r = E * c - k ^ 2
  c_ne : c ≠ 0
  P_pos : 0 < P
  E_mod : E % 16 = 6
  c_odd : c % 2 = 1

/-! Coprimality for the Dirichlet progressions. The residues `R` of the case
`B = 1` satisfy `R + 1 = Kn`, are odd, and are 2 modulo 5. These facts
make `R` invertible modulo `160n`, the common modulus of the conditions
modulo `32n` and modulo 5. -/

/-- If `R` is odd, `R ≡ 2 (mod 5)`, and `R` is prime to `n`, then `R` is prime
to `160n`. -/
theorem coprime_mul_of_odd_of_mod_five {n R : ℕ} (hodd : R % 2 = 1) (hfive : R % 5 = 2)
    (hnr : R.Coprime n) : R.Coprime (160 * n) := by
  have hr2 : R.Coprime 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro hd
    obtain ⟨q, hq⟩ := hd
    omega
  have hr32 : R.Coprime 32 := by
    have hp := Nat.Coprime.pow_right 5 hr2
    norm_num at hp ⊢
    exact hp
  have hr5 : R.Coprime 5 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
    intro hd
    obtain ⟨q, hq⟩ := hd
    omega
  have hall : R.Coprime ((32 * n) * 5) := (hr32.mul_right hnr).mul_right hr5
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hall

/-- Coprimality for the case `B = 1`: if `R + 1 = Kn`, `R` is odd, and
`R ≡ 2 (mod 5)`, then `R` is prime to `160n`. -/
theorem progressionResidue_coprime (n R K : ℕ)
    (hlin : R + 1 = K * n) (hodd : R % 2 = 1) (hfive : R % 5 = 2) :
    R.Coprime (160 * n) := by
  refine coprime_mul_of_odd_of_mod_five hodd hfive ?_
  apply Nat.Coprime.symm
  apply Nat.Coprime.of_dvd_left
    (show n ∣ R + 1 by exact ⟨K, by simpa [Nat.mul_comm] using hlin⟩)
  simp

/-- The `PrimeProgression` modulo `160n` for the case `B = 1`, combining the
conditions modulo `32n` and modulo 5. Coprimality of the residue comes from
`progressionResidue_coprime`. -/
def bOnePrimeProgression (n R K : ℕ) (hn : 0 < n)
    (hlin : R + 1 = K * n) (hodd : R % 2 = 1) (hfive : R % 5 = 2) :
    MordellRegularity.PrimeProgression (fun p ↦ p ≡ R [MOD 160 * n]) where
  modulus := 160 * n
  residue := R
  modulus_ne_zero := by omega
  residue_coprime := progressionResidue_coprime n R K hlin hodd hfive
  forces := by intro p hp; exact hp

/-- Coprimality for the case `B = 5`: if `R + 5 = Ks`, `R` is odd, and
`R ≡ 2 (mod 5)`, then `R` is prime to `160s`. The condition `R ≡ 2 (mod 5)`
excludes the common factor 5 that the constant 5 could introduce. -/
theorem fiveProgressionResidue_coprime (s R K : ℕ)
    (hlin : R + 5 = K * s) (hodd : R % 2 = 1) (hfive : R % 5 = 2) :
    R.Coprime (160 * s) := by
  have h5R : (5 : ℕ).Coprime R := by
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
    intro hd
    obtain ⟨q, hq⟩ := hd
    omega
  have hsum : (R + 5).Coprime R := by
    simpa [Nat.add_comm] using h5R
  have hsr : s.Coprime R := by
    apply Nat.Coprime.of_dvd_left
      (show s ∣ R + 5 by exact ⟨K, by simpa [Nat.mul_comm] using hlin⟩)
    exact hsum
  exact coprime_mul_of_odd_of_mod_five hodd hfive hsr.symm

/-- The `PrimeProgression` modulo `160s` for the case `B = 5`, combining the
conditions modulo `32s` and modulo 5. -/
def bFivePrimeProgression (s R K : ℕ) (hs : 0 < s)
    (hlin : R + 5 = K * s) (hodd : R % 2 = 1) (hfive : R % 5 = 2) :
    MordellRegularity.PrimeProgression (fun p ↦ p ≡ R [MOD 160 * s]) where
  modulus := 160 * s
  residue := R
  modulus_ne_zero := by omega
  residue_coprime := fiveProgressionResidue_coprime s R K hlin hodd hfive
  forces := by intro p hp; exact hp

/-! The residue rows. The four residues of the case `B = 1` correspond to
`n ≡ 1, 2, 3, 4 (mod 5)`; the two residues of the case `B = 5` correspond to
the nonexceptional classes `s ≡ 2, 3 (mod 5)`. Each row is one invertible
progression modulo `160n` or `160s`, to which Dirichlet's theorem applies. -/

/-- The row `n ≡ 1 (mod 5)` of the case `B = 1`: the progression of residue
`2n - 1 + 32n · 3` modulo `160n`. Its members are `≡ 2n - 1 (mod 32n)` and
`≡ 2 (mod 5)`. -/
def bOneProgressionModOne (n : ℕ) (hn : 0 < n) (h5 : n % 5 = 1) :=
  bOnePrimeProgression n (2 * n - 1 + 32 * n * 3) 98 hn
    (by omega) (by omega) (by omega)

/-- The row `n ≡ 2 (mod 5)` of the case `B = 1`: the progression of residue
`2n - 1 + 32n` modulo `160n`. Its members are `≡ 2n - 1 (mod 32n)` and
`≡ 2 (mod 5)`. -/
def bOneProgressionModTwo (n : ℕ) (hn : 0 < n) (h5 : n % 5 = 2) :=
  bOnePrimeProgression n (2 * n - 1 + 32 * n) 34 hn
    (by omega) (by omega) (by omega)

/-- The row `n ≡ 3 (mod 5)` of the case `B = 1`: the progression of residue
`2n - 1 + 32n · 2` modulo `160n`. Its members are `≡ 2n - 1 (mod 32n)` and
`≡ 2 (mod 5)`. -/
def bOneProgressionModThree (n : ℕ) (hn : 0 < n) (h5 : n % 5 = 3) :=
  bOnePrimeProgression n (2 * n - 1 + 32 * n * 2) 66 hn
    (by omega) (by omega) (by omega)

/-- The row `n ≡ 4 (mod 5)` of the case `B = 1`: the progression of residue
`2n - 1` modulo `160n`. Its members are `≡ 2n - 1 (mod 32n)` and
`≡ 2 (mod 5)`. -/
def bOneProgressionModFour (n : ℕ) (hn : 0 < n) (h5 : n % 5 = 4) :=
  bOnePrimeProgression n (2 * n - 1) 2 hn
    (by omega) (by omega) (by omega)

/-- The row `s ≡ 2 (mod 5)` of the case `B = 5`: the progression of residue
`2s - 5 + 32s · 2` modulo `160s`. Its members are `≡ 2s - 5 (mod 32s)` and
`≡ 2 (mod 5)`. -/
def bFiveProgressionModTwo (s : ℕ) (hs : 3 ≤ s) (h5 : s % 5 = 2) :=
  bFivePrimeProgression s (2 * s - 5 + 32 * s * 2) 66 (by omega)
    (by omega) (by omega) (by omega)

/-- The row `s ≡ 3 (mod 5)` of the case `B = 5`: the progression of residue
`2s - 5 + 32s` modulo `160s`. Its members are `≡ 2s - 5 (mod 32s)` and
`≡ 2 (mod 5)`. -/
def bFiveProgressionModThree (s : ℕ) (hs : 3 ≤ s) (h5 : s % 5 = 3) :=
  bFivePrimeProgression s (2 * s - 5 + 32 * s) 34 (by omega)
    (by omega) (by omega) (by omega)

/-- Dirichlet's theorem for one row: if `R` is prime to `160n`,
`R + b = 2n(1 + 16t)`, and `R ≡ 2 (mod 5)`, then some prime `p ≡ 2 (mod 5)`
has the form `p = 2nc - b` with `c ≡ 1 (mod 16)`. -/
theorem exists_prime_from_linear_row (n R t b : ℕ)
    (hn : 0 < n) (hcop : R.Coprime (160 * n))
    (hlin : R + b = 2 * n * (1 + 16 * t)) (hfive : R % 5 = 2) :
    ∃ p : ℕ, ∃ c : ℤ, p.Prime ∧ 0 < (p : ℤ) ∧
      c % 16 = 1 ∧ (p : ℤ) = 2 * n * c - b ∧ (p : ℤ) % 5 = 2 := by
  obtain ⟨p, k, hp, hpk⟩ :=
    MordellRegularity.exists_auxiliary_prime_eq_add_mul
      (160 * n) R (by omega) hcop
  let c : ℤ := 1 + 16 * (t : ℤ) + 80 * (k : ℤ)
  have hlinZ : (R : ℤ) + b = 2 * n * (1 + 16 * (t : ℤ)) := by
    exact_mod_cast hlin
  have hpkZ : (p : ℤ) = R + 160 * n * (k : ℤ) := by
    exact_mod_cast hpk
  have hfiveZ : (R : ℤ) % 5 = 2 := by exact_mod_cast hfive
  refine ⟨p, c, hp, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hp.pos
  · dsimp [c]
    norm_num [Int.add_emod, Int.mul_emod]
  · dsimp [c]
    nlinarith [hlinZ, hpkZ]
  · rw [hpkZ]
    norm_num [Int.add_emod, Int.mul_emod, hfiveZ]

/-- The prime of the case `B = 1`: for `n > 0` with `5 ∤ n`, some prime
`p ≡ 2 (mod 5)` has the form `p = 2nc - 1` with `c ≡ 1 (mod 16)`. The square
root comes from reciprocity below. -/
theorem exists_bOne_prime (n : ℕ) (hn : 0 < n) (hfive : n % 5 ≠ 0) :
    ∃ p : ℕ, ∃ c : ℤ, p.Prime ∧ 0 < (p : ℤ) ∧
      c % 16 = 1 ∧ (p : ℤ) = 2 * n * c - 1 ∧ (p : ℤ) % 5 = 2 := by
  have hres : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hres with hres | hres | hres | hres
  · exact exists_prime_from_linear_row n (2 * n - 1 + 32 * n * 3) 3 1 hn
      (bOneProgressionModOne n hn hres).residue_coprime (by omega) (by omega)
  · exact exists_prime_from_linear_row n (2 * n - 1 + 32 * n) 1 1 hn
      (bOneProgressionModTwo n hn hres).residue_coprime (by omega) (by omega)
  · exact exists_prime_from_linear_row n (2 * n - 1 + 32 * n * 2) 2 1 hn
      (bOneProgressionModThree n hn hres).residue_coprime (by omega) (by omega)
  · exact exists_prime_from_linear_row n (2 * n - 1) 0 1 hn
      (bOneProgressionModFour n hn hres).residue_coprime (by omega) (by omega)

/-- The prime of the case `B = 5`: for `s ≥ 3` with `s ≡ 2, 3 (mod 5)`,
some prime `p ≡ 2 (mod 5)` has the form `p = 2sc - 5` with
`c ≡ 1 (mod 16)`. -/
theorem exists_bFive_prime (s : ℕ) (hs : 3 ≤ s)
    (hfive : s % 5 = 2 ∨ s % 5 = 3) :
    ∃ p : ℕ, ∃ c : ℤ, p.Prime ∧ 0 < (p : ℤ) ∧
      c % 16 = 1 ∧ (p : ℤ) = 2 * s * c - 5 ∧ (p : ℤ) % 5 = 2 := by
  rcases hfive with hfive | hfive
  · exact exists_prime_from_linear_row s (2 * s - 5 + 32 * s * 2) 2 5 (by omega)
      (bFiveProgressionModTwo s hs hfive).residue_coprime (by omega) (by omega)
  · exact exists_prime_from_linear_row s (2 * s - 5 + 32 * s) 1 5 (by omega)
      (bFiveProgressionModThree s hs hfive).residue_coprime (by omega) (by omega)

/-- For `s ≡ 3 (mod 4)`, the Jacobi symbol `(-5/s)` equals `-(s/5)`; `s`
need not be prime. -/
theorem jacobi_neg_five_of_three_mod_four {s : ℕ} (hs : s % 4 = 3) :
    jacobiSym (-5) s = -jacobiSym (s : ℤ) 5 := by
  have hsodd : Odd s := Nat.odd_iff.mpr (by omega)
  rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) by norm_num,
    jacobiSym.neg _ hsodd, ZMod.χ₄_nat_three_mod_four hs,
    jacobiSym.quadratic_reciprocity_one_mod_four
      (by norm_num : (5 : ℕ) % 4 = 1) hsodd]
  ring

/-- Reciprocity for the case `B = 5`: if `s ≡ 3 (mod 4)`, `s ≡ 2, 3 (mod 5)`,
`p ≡ 1 (mod 4)`, and `p ≡ -5 (mod s)`, then `(-s/p) = 1`. The computation
uses Jacobi symbols, so `s` need not be squarefree. -/
theorem bFive_jacobi_reciprocity {s p : ℕ}
    (hs : s % 4 = 3) (hp : p % 4 = 1)
    (hsfive : s % 5 = 2 ∨ s % 5 = 3)
    (hps : (p : ℤ) ≡ -5 [ZMOD (s : ℤ)]) :
    jacobiSym (-(s : ℤ)) p = 1 := by
  have hsodd : Odd s := Nat.odd_iff.mpr (by omega)
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hpodd, ZMod.χ₄_nat_one_mod_four hp, one_mul,
    jacobiSym.quadratic_reciprocity_one_mod_four' hsodd hp,
    jacobiSym.mod_left' hps, jacobi_neg_five_of_three_mod_four hs,
    jacobiSym.mod_left]
  rcases hsfive with h | h
  · have hz : (s : ℤ) % 5 = 2 := by exact_mod_cast h
    norm_num [hz]
  · have hz : (s : ℤ) % 5 = 3 := by exact_mod_cast h
    norm_num [hz]

/-- Reciprocity for the case `B = 1`: if `n ≡ 3 (mod 4)`, `p ≡ 1 (mod 4)`,
`p ≡ 2 (mod 5)`, and `p ≡ -1 (mod n)`, then `(-5n/p) = 1`. The factors
`(-5/p) = -1` and `(n/p) = -1` cancel. -/
theorem bOne_jacobi_reciprocity {n p : ℕ}
    (hn : n % 4 = 3) (hp : p % 4 = 1) (hpfive : p % 5 = 2)
    (hpn : (p : ℤ) ≡ -1 [ZMOD (n : ℤ)]) :
    jacobiSym (-(5 * (n : ℤ))) p = 1 := by
  have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hfive : jacobiSym (-5) p = -1 := by
    rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) by norm_num,
      jacobiSym.neg _ hpodd, ZMod.χ₄_nat_one_mod_four hp, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four
        (by norm_num : (5 : ℕ) % 4 = 1) hpodd,
      jacobiSym.mod_left]
    have hz : (p : ℤ) % 5 = 2 := by exact_mod_cast hpfive
    norm_num [hz]
  have hnleg : jacobiSym (n : ℤ) p = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hnodd hp,
      jacobiSym.mod_left' hpn,
      show (-1 : ℤ) = -(1 : ℤ) by norm_num,
      jacobiSym.neg _ hnodd, ZMod.χ₄_nat_three_mod_four hn]
    simp
  rw [show -(5 * (n : ℤ)) = (-5) * (n : ℤ) by ring,
    jacobiSym.mul_left, hfive, hnleg]
  norm_num

/-! ## Roots, quotients, and the choice of `k`

Reciprocity gives one divisibility, and the CRT choice of `k` gives two more.
The lemmas below turn them into the quotient equations of `BOneRootData` and
`BFiveRootData`.
-/

/-- If `p ∣ L² + 10c`, then `pr - L² = 10c` for some `r`. -/
theorem bOne_root_quotient {p L c : ℤ} (h : p ∣ L ^ 2 + 10 * c) :
    ∃ r : ℤ, p * r - L ^ 2 = 10 * c := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  nlinarith

/-- If `P ∣ 5d² + 2c`, then `Pr - 5d² = 2c` for some `r`. -/
theorem bFive_root_quotient {P d c : ℤ} (h : P ∣ 5 * d ^ 2 + 2 * c) :
    ∃ r : ℤ, P * r - 5 * d ^ 2 = 2 * c := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  nlinarith

/-- If `c ∣ L + k` and `c ∣ r + k²`, then `L = cA - k` and `r = Ec - k²` for
some integers `A` and `E`. The cases `B = 1` and `B = 5` both use this. -/
theorem crt_quotients {c L r k : ℤ}
    (hA : c ∣ L + k) (hE : c ∣ r + k ^ 2) :
    ∃ A E : ℤ, L = c * A - k ∧ r = E * c - k ^ 2 := by
  obtain ⟨A, hA⟩ := hA
  obtain ⟨E, hE⟩ := hE
  refine ⟨A, E, ?_, ?_⟩ <;> nlinarith

/-- In the case `B = 1`, the divisibility `c ∣ r + k²` follows from
`c ∣ L + k`: `p = 2nc - 1` turns the root equation into `c ∣ r + L²`, and
`c ∣ L + k` gives `c ∣ k² - L²`. -/
theorem bOne_E_divisibility {n c p L r k : ℤ}
    (hp : p = 2 * n * c - 1)
    (hr : p * r - L ^ 2 = 10 * c)
    (hk : c ∣ L + k) : c ∣ r + k ^ 2 := by
  obtain ⟨t, ht⟩ := hk
  have hbase : r + L ^ 2 = c * (2 * n * r - 10) := by
    rw [hp] at hr
    calc
      r + L ^ 2 = 2 * n * c * r - 10 * c := by nlinarith
      _ = c * (2 * n * r - 10) := by ring
  refine ⟨(2 * n * r - 10) + (k - L) * t, ?_⟩
  calc
    r + k ^ 2 = (r + L ^ 2) + (k - L) * (k + L) := by ring
    _ = c * (2 * n * r - 10) + (k - L) * (c * t) := by
      rw [hbase]
      rw [← ht]
      ring
    _ = c * ((2 * n * r - 10) + (k - L) * t) := by ring

/-- For an odd modulus `p = 2q + 1`, every `x` has a translate `x + pt`
divisible by 4. This chooses the representative of the root `L` (or
`d`). -/
theorem exists_odd_modulus_shift_to_four (x p q : ℤ) (hp : p = 2 * q + 1) :
    ∃ t : ℤ, (x + p * t) % 4 = 0 := by
  refine ⟨-x * p, Int.dvd_iff_emod_eq_zero.mp ?_⟩
  refine ⟨-x * q * (q + 1), ?_⟩
  rw [hp]
  ring

/-- An explicit CRT solution: for odd `c`, `crtK L c` is congruent to `-L`
modulo `c` and to 2 modulo 4. -/
def crtK (L c : ℤ) : ℤ := -L + c * (c * (L + 2))

/-- `c ∣ L + crtK L c`. -/
theorem c_dvd_L_add_crtK (L c : ℤ) : c ∣ L + crtK L c := by
  exact ⟨c * (L + 2), by simp [crtK]⟩

/-- For odd `c`, `crtK L c ≡ 2 (mod 4)`. -/
theorem crtK_mod_four (L c q : ℤ) (hc : c = 2 * q + 1) :
    crtK L c % 4 = 2 := by
  have hdiv : (4 : ℤ) ∣ crtK L c - 2 := by
    refine ⟨q * (q + 1) * (L + 2), ?_⟩
    rw [hc]
    simp [crtK]
    ring
  change Int.ModEq 4 (crtK L c) 2
  exact (Int.modEq_iff_dvd.mpr hdiv).symm

/-- The separator in the case `B = 1`: if `p ≡ 5, 13 (mod 16)`,
`c ≡ 1 (mod 16)`, `L² ≡ 0 (mod 16)`, and `k² ≡ 4 (mod 16)`, then the two
quotient equations force `E ≡ 6 (mod 16)`. -/
theorem bOne_separator_of_root_equations {p c L r k E : ℤ}
    (hp : p % 16 = 5 ∨ p % 16 = 13) (hc : c % 16 = 1)
    (hL : L ^ 2 % 16 = 0) (hk : k ^ 2 % 16 = 4)
    (hroot : p * r - L ^ 2 = 10 * c)
    (hquot : r = E * c - k ^ 2) : E % 16 = 6 := by
  have hrootmod := congrArg (fun z : ℤ => z % 16) hroot
  have hquotmod := congrArg (fun z : ℤ => z % 16) hquot
  rcases hp with hp | hp <;>
    norm_num [Int.sub_emod, Int.mul_emod, hp, hc, hL, hk]
      at hrootmod hquotmod <;> omega

/-- If `n ≡ 3 (mod 4)` and `c ≡ 1 (mod 16)`, then `p = 2nc - 1` is 5 or
13 modulo 16, the residues used by `bOne_separator_of_root_equations`. -/
theorem bOne_prime_mod_sixteen {n c p : ℤ}
    (hn : n % 4 = 3) (hc : c % 16 = 1)
    (hp : p = 2 * n * c - 1) : p % 16 = 5 ∨ p % 16 = 13 := by
  have hn16 : n % 16 = 3 ∨ n % 16 = 7 ∨
      n % 16 = 11 ∨ n % 16 = 15 := by omega
  rw [hp]
  rcases hn16 with hn16 | hn16 | hn16 | hn16 <;>
    norm_num [Int.sub_emod, Int.mul_emod, hc, hn16]

/-- The square of a multiple of 4 is 0 modulo 16. -/
theorem square_mod_sixteen_of_zero_mod_four {x : ℤ} (hx : x % 4 = 0) :
    x ^ 2 % 16 = 0 := by
  obtain ⟨k, hk⟩ := Int.dvd_iff_emod_eq_zero.mpr hx
  have hs : x ^ 2 = 16 * k ^ 2 := by rw [hk]; ring
  rw [hs]
  simp

/-- If `x ≡ 2 (mod 4)`, then `x² ≡ 4 (mod 16)`. -/
theorem square_mod_sixteen_of_two_mod_four {x : ℤ} (hx : x % 4 = 2) :
    x ^ 2 % 16 = 4 := by
  have hx0 : (x - 2) % 4 = 0 := by omega
  obtain ⟨k, hk⟩ := Int.dvd_iff_emod_eq_zero.mpr hx0
  have heq : x = 4 * k + 2 := by omega
  have hs : x ^ 2 = 16 * (k ^ 2 + k) + 4 := by rw [heq]; ring
  rw [hs]
  norm_num [Int.add_emod, Int.mul_emod]

/-- Let `n ≡ 3 (mod 4)`, `c ≡ 1 (mod 16)`, and `p = 2nc - 1 > 0`. A square
root `L ≡ 0 (mod 4)` of `-10c` modulo `p` gives `BOneRootData n`: the
quotients, the coordinate `k`, and the separator are derived from it. -/
theorem bOneRootData_of_prime_root {n c p L : ℤ}
    (hn : n % 4 = 3) (hc : c % 16 = 1)
    (hp : p = 2 * n * c - 1) (hppos : 0 < p)
    (hL : L % 4 = 0) (hroot : p ∣ L ^ 2 + 10 * c) :
    Nonempty (BOneRootData n) := by
  obtain ⟨r, hr⟩ := bOne_root_quotient hroot
  let k := crtK L c
  have hck : c ∣ L + k := c_dvd_L_add_crtK L c
  obtain ⟨A, E, hA, hE⟩ :=
    crt_quotients hck (bOne_E_divisibility hp hr hck)
  have hcodd : c % 2 = 1 := by omega
  have hc0 : (c - 1) % 2 = 0 := by omega
  obtain ⟨q, hq⟩ := Int.dvd_iff_emod_eq_zero.mpr hc0
  have hcform : c = 2 * q + 1 := by omega
  have hk : k % 4 = 2 := crtK_mod_four L c q hcform
  have hEmod : E % 16 = 6 :=
    bOne_separator_of_root_equations (bOne_prime_mod_sixteen hn hc hp) hc
      (square_mod_sixteen_of_zero_mod_four hL)
      (square_mod_sixteen_of_two_mod_four hk) hr hE
  exact ⟨{
    c := c, p := p, L := L, r := r, k := k, E := E, A := A
    p_eq := hp, root_eq := hr, L_eq := hA, r_eq := hE
    c_ne := by
      intro hzero
      rw [hzero] at hc
      norm_num at hc
    p_pos := hppos, E_mod := hEmod, c_odd := hcodd
  }⟩

/-- If `5 ∤ c` and `c ∣ 5x`, then `c ∣ x`. This cancels the forced factor
5 in the case `B = 5`; the prime progression gives `5 ∤ c`. -/
theorem dvd_of_dvd_five_mul {c x : ℤ} (hc : c % 5 ≠ 0)
    (hx : c ∣ 5 * x) : c ∣ x := by
  obtain ⟨t, ht⟩ := hx
  have hm := congrArg (fun z : ℤ => z % 5) ht
  have hclo : 0 ≤ c % 5 := Int.emod_nonneg _ (by norm_num)
  have hchi : c % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  have htlo : 0 ≤ t % 5 := Int.emod_nonneg _ (by norm_num)
  have hthi : t % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  have htmod : t % 5 = 0 := by
    generalize hcr : c % 5 = cr at hc hclo hchi hm
    generalize htr : t % 5 = tr at htlo hthi hm ⊢
    interval_cases cr <;> interval_cases tr <;>
      norm_num [Int.mul_emod, hcr, htr] at hm <;> omega
  obtain ⟨u, hu⟩ := Int.dvd_iff_emod_eq_zero.mpr htmod
  refine ⟨u, ?_⟩
  rw [hu] at ht
  nlinarith

/-- In the case `B = 5`, the divisibility `c ∣ r + k²` follows from
`c ∣ d + k` after cancelling the factor 5. -/
theorem bFive_E_divisibility {s c P d r k : ℤ}
    (hP : P = 2 * s * c - 5)
    (hr : P * r - 5 * d ^ 2 = 2 * c)
    (hc : c % 5 ≠ 0) (hk : c ∣ d + k) : c ∣ r + k ^ 2 := by
  have hbase : c ∣ 5 * (r + d ^ 2) := by
    refine ⟨2 * s * r - 2, ?_⟩
    rw [hP] at hr
    nlinarith
  obtain ⟨u, hu⟩ := dvd_of_dvd_five_mul hc hbase
  obtain ⟨t, ht⟩ := hk
  refine ⟨u + (k - d) * t, ?_⟩
  calc
    r + k ^ 2 = (r + d ^ 2) + (k - d) * (d + k) := by ring
    _ = c * u + (k - d) * (c * t) := by rw [hu, ht]
    _ = c * (u + (k - d) * t) := by ring

/-- If `P = 2sc - 5` and `P ≡ 2 (mod 5)`, then `5 ∤ c`. -/
theorem bFive_c_mod_five_ne_zero {s c P : ℤ}
    (hP : P = 2 * s * c - 5) (hpmod : P % 5 = 2) : c % 5 ≠ 0 := by
  intro hc
  rw [hP] at hpmod
  norm_num [Int.sub_emod, Int.mul_emod, hc] at hpmod

/-- If `s ≡ 3 (mod 4)` and `c ≡ 1 (mod 16)`, then `P = 2sc - 5` is 1 or
9 modulo 16, the residues used by `bFive_separator_of_root_equations`. -/
theorem bFive_prime_mod_sixteen {s c P : ℤ}
    (hs : s % 4 = 3) (hc : c % 16 = 1)
    (hP : P = 2 * s * c - 5) : P % 16 = 1 ∨ P % 16 = 9 := by
  have hs16 : s % 16 = 3 ∨ s % 16 = 7 ∨
      s % 16 = 11 ∨ s % 16 = 15 := by omega
  rw [hP]
  rcases hs16 with hs16 | hs16 | hs16 | hs16 <;>
    norm_num [Int.sub_emod, Int.mul_emod, hc, hs16]

/-- The separator in the case `B = 5`: if `P ≡ 1, 9 (mod 16)`,
`c ≡ 1 (mod 16)`, `d² ≡ 0 (mod 16)`, and `k² ≡ 4 (mod 16)`, then the reduced
root equation and the quotient equation force `E ≡ 6 (mod 16)`. -/
theorem bFive_separator_of_root_equations {P c d r k E : ℤ}
    (hP : P % 16 = 1 ∨ P % 16 = 9) (hc : c % 16 = 1)
    (hd : d ^ 2 % 16 = 0) (hk : k ^ 2 % 16 = 4)
    (hroot : P * r - 5 * d ^ 2 = 2 * c)
    (hquot : r = E * c - k ^ 2) : E % 16 = 6 := by
  have hrootmod := congrArg (fun z : ℤ => z % 16) hroot
  have hquotmod := congrArg (fun z : ℤ => z % 16) hquot
  rcases hP with hP | hP <;>
    norm_num [Int.sub_emod, Int.mul_emod, hP, hc, hd, hk]
      at hrootmod hquotmod <;> omega

/-- Let `s ≡ 3 (mod 4)`, `c ≡ 1 (mod 16)`, and `P = 2sc - 5 > 0` with
`P ≡ 2 (mod 5)`. A root `d ≡ 0 (mod 4)` with `P ∣ 5d² + 2c` gives
`BFiveRootData s`. In the application `exists_bFive_prime` supplies
`P ≡ 2 (mod 5)`. -/
theorem bFiveRootData_of_prime_root {s c P d : ℤ}
    (hs : s % 4 = 3) (hc : c % 16 = 1)
    (hP : P = 2 * s * c - 5) (hPpos : 0 < P)
    (hPfive : P % 5 = 2) (hd : d % 4 = 0)
    (hroot : P ∣ 5 * d ^ 2 + 2 * c) :
    Nonempty (BFiveRootData s) := by
  obtain ⟨r, hr⟩ := bFive_root_quotient hroot
  let k := crtK d c
  have hck : c ∣ d + k := c_dvd_L_add_crtK d c
  have hcfive : c % 5 ≠ 0 := bFive_c_mod_five_ne_zero hP hPfive
  obtain ⟨v, E, hv, hE⟩ :=
    crt_quotients hck (bFive_E_divisibility hP hr hcfive hck)
  have hcodd : c % 2 = 1 := by omega
  have hc0 : (c - 1) % 2 = 0 := by omega
  obtain ⟨q, hq⟩ := Int.dvd_iff_emod_eq_zero.mpr hc0
  have hcform : c = 2 * q + 1 := by omega
  have hk : k % 4 = 2 := crtK_mod_four d c q hcform
  have hEmod : E % 16 = 6 :=
    bFive_separator_of_root_equations (bFive_prime_mod_sixteen hs hc hP) hc
      (square_mod_sixteen_of_zero_mod_four hd)
      (square_mod_sixteen_of_two_mod_four hk) hr hE
  exact ⟨{
    c := c, P := P, d := d, r := r, k := k, E := E, v := v
    P_eq := hP, root_eq := hr, d_eq := hv, r_eq := hE
    c_ne := by
      intro hzero
      rw [hzero] at hc
      norm_num at hc
    P_pos := hPpos, E_mod := hEmod, c_odd := hcodd
  }⟩

/-- For an odd modulus `p`, a solution of `p ∣ D x² + e` can be chosen
divisible by 4. -/
theorem exists_root_zero_mod_four {p q D e x : ℤ}
    (hp : p = 2 * q + 1) (hx : p ∣ D * x ^ 2 + e) :
    ∃ y : ℤ, y % 4 = 0 ∧ p ∣ D * y ^ 2 + e := by
  obtain ⟨t, ht⟩ := exists_odd_modulus_shift_to_four x p q hp
  obtain ⟨v, hv⟩ := hx
  refine ⟨x + p * t, ht, v + D * (2 * x * t + p * t ^ 2), ?_⟩
  calc
    D * (x + p * t) ^ 2 + e =
        (D * x ^ 2 + e) + p * (D * (2 * x * t + p * t ^ 2)) := by ring
    _ = p * (v + D * (2 * x * t + p * t ^ 2)) := by rw [hv]; ring

/-- Any square root of `-10c` modulo `p = 2nc - 1` gives `BOneRootData n`;
the root is first shifted to a multiple of 4. -/
theorem bOneRootData_of_root {n c p x : ℤ}
    (hn : n % 4 = 3) (hc : c % 16 = 1)
    (hp : p = 2 * n * c - 1) (hppos : 0 < p)
    (hroot : p ∣ x ^ 2 + 10 * c) :
    Nonempty (BOneRootData n) := by
  have hpodd : p = 2 * (n * c - 1) + 1 := by rw [hp]; ring
  obtain ⟨L, hL, hLroot⟩ := exists_root_zero_mod_four
    (D := 1) (e := 10 * c) hpodd (by simpa using hroot)
  exact bOneRootData_of_prime_root hn hc hp hppos hL (by simpa using hLroot)

/-- Any solution of `P ∣ 5x² + 2c` gives `BFiveRootData s`, after the same
shift to a multiple of 4. -/
theorem bFiveRootData_of_root {s c P x : ℤ}
    (hs : s % 4 = 3) (hc : c % 16 = 1)
    (hP : P = 2 * s * c - 5) (hPpos : 0 < P)
    (hPfive : P % 5 = 2) (hroot : P ∣ 5 * x ^ 2 + 2 * c) :
    Nonempty (BFiveRootData s) := by
  have hPodd : P = 2 * (s * c - 3) + 1 := by rw [hP]; ring
  obtain ⟨d, hd, hdroot⟩ := exists_root_zero_mod_four hPodd hroot
  exact bFiveRootData_of_prime_root hs hc hP hPpos hPfive hd hdroot

/-- A binary completion `pu - 5nt² = 1` with `p = 2nc - 1` gives the square
root `5t` of `-10c` modulo `p`. -/
theorem bOne_root_of_binary_completion {n c p u t : ℤ}
    (hp : p = 2 * n * c - 1) (hu : p * u - 5 * n * t ^ 2 = 1) :
    p ∣ (5 * t) ^ 2 + 10 * c := by
  refine ⟨10 * c * u - 25 * t ^ 2, ?_⟩
  linear_combination -10 * c * hu + 25 * t ^ 2 * hp

/-- A binary completion `pu - st² = 1` with `p = 2sc - 5` gives
`p ∣ 5t² + 2c`, with no rescaling of `t`. -/
theorem bFive_root_of_binary_completion {s c p u t : ℤ}
    (hp : p = 2 * s * c - 5) (hu : p * u - s * t ^ 2 = 1) :
    p ∣ 5 * t ^ 2 + 2 * c := by
  refine ⟨2 * c * u - t ^ 2, ?_⟩
  linear_combination -2 * c * hu + t ^ 2 * hp

/-- Let `p = 2nc - 1` be a prime with `n ≡ 3 (mod 4)` and
`c ≡ 1 (mod 16)`. If `p ∤ 5n` and `(-5n/p) = 1`, then `BOneRootData n`
holds. Below, `nonzero_of_neg_legendre_one` derives `p ∤ 5n` from the
Legendre symbol. -/
theorem bOneRootData_of_legendre {n p : ℕ} [Fact p.Prime] {c : ℤ}
    (hn : n % 4 = 3) (hc : c % 16 = 1)
    (hp : (p : ℤ) = 2 * n * c - 1) (hppos : 0 < (p : ℤ))
    (hd : (((5 * n : ℕ) : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-((5 * n : ℕ) : ℤ)) = 1) :
    Nonempty (BOneRootData (n : ℤ)) := by
  obtain ⟨u, t, hut⟩ :=
    MordellRegularity.exists_binary_unit_completion_of_legendre hd hleg
  have hu : (p : ℤ) * u - 5 * (n : ℤ) * t ^ 2 = 1 := by
    simpa [Nat.cast_mul] using hut
  exact bOneRootData_of_root (by exact_mod_cast hn) hc hp hppos
    (bOne_root_of_binary_completion hp hu)

/-- Let `p = 2sc - 5` be a prime with `p ≡ 2 (mod 5)`, `s ≡ 3 (mod 4)`, and
`c ≡ 1 (mod 16)`. If `p ∤ s` and `(-s/p) = 1`, then `BFiveRootData s`
holds. -/
theorem bFiveRootData_of_legendre {s p : ℕ} [Fact p.Prime] {c : ℤ}
    (hs : s % 4 = 3) (hc : c % 16 = 1)
    (hp : (p : ℤ) = 2 * s * c - 5) (hppos : 0 < (p : ℤ))
    (hpfive : (p : ℤ) % 5 = 2)
    (hd : ((s : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-(s : ℤ)) = 1) :
    Nonempty (BFiveRootData (s : ℤ)) := by
  obtain ⟨u, t, hut⟩ :=
    MordellRegularity.exists_binary_unit_completion_of_legendre hd hleg
  exact bFiveRootData_of_root (by exact_mod_cast hs) hc hp hppos hpfive
    (bFive_root_of_binary_completion hp hut)

/-- If `(-a/p) = 1`, then `a` is nonzero modulo `p`. -/
theorem nonzero_of_neg_legendre_one {p : ℕ} [Fact p.Prime] {a : ℤ}
    (h : legendreSym p (-a) = 1) : (a : ZMod p) ≠ 0 := by
  intro ha
  have hz : legendreSym p (-a) = 0 :=
    (legendreSym.eq_zero_iff p (-a)).mpr (by simp only [Int.cast_neg, ha, neg_zero])
  omega

/-- For `n ≡ 3 (mod 4)` with `5 ∤ n`, Dirichlet's theorem and reciprocity
give `BOneRootData n`. -/
theorem bOneRootData_exists_nat {n : ℕ} (hn : n % 4 = 3)
    (hfive : n % 5 ≠ 0) : Nonempty (BOneRootData (n : ℤ)) := by
  obtain ⟨p, c, hpprime, hppos, hc, hp, hpfive⟩ :=
    exists_bOne_prime n (by omega) hfive
  let _ : Fact p.Prime := ⟨hpprime⟩
  have hp16 := bOne_prime_mod_sixteen (by exact_mod_cast hn) hc hp
  have hp4z : (p : ℤ) % 4 = 1 := by omega
  have hp4 : p % 4 = 1 := by exact_mod_cast hp4z
  have hp5 : p % 5 = 2 := by exact_mod_cast hpfive
  have hpn : (p : ℤ) ≡ -1 [ZMOD (n : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-2 * c, ?_⟩
    rw [hp]
    ring
  have hleg : legendreSym p (-((5 * n : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      bOne_jacobi_reciprocity hn hp4 hp5 hpn
  exact bOneRootData_of_legendre hn hc hp hppos
    (nonzero_of_neg_legendre_one hleg) hleg

/-- For `s ≡ 3 (mod 4)` with `s ≡ 2, 3 (mod 5)`, Dirichlet's theorem and
reciprocity give `BFiveRootData s`. -/
theorem bFiveRootData_exists_nat {s : ℕ} (hs : s % 4 = 3)
    (hfive : s % 5 = 2 ∨ s % 5 = 3) :
    Nonempty (BFiveRootData (s : ℤ)) := by
  obtain ⟨p, c, hpprime, hppos, hc, hp, hpfive⟩ :=
    exists_bFive_prime s (by omega) hfive
  let _ : Fact p.Prime := ⟨hpprime⟩
  have hp16 := bFive_prime_mod_sixteen (by exact_mod_cast hs) hc hp
  have hp4z : (p : ℤ) % 4 = 1 := by omega
  have hp4 : p % 4 = 1 := by exact_mod_cast hp4z
  have hps : (p : ℤ) ≡ -5 [ZMOD (s : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-2 * c, ?_⟩
    rw [hp]
    ring
  have hleg : legendreSym p (-(s : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    exact bFive_jacobi_reciprocity hs hp4 hfive hps
  exact bFiveRootData_of_legendre hs hc hp hppos hpfive
    (nonzero_of_neg_legendre_one hleg) hleg

/-- If `25 ∤ 10s` and `10s` is not exceptional, then `s ≡ 2, 3 (mod 5)`:
the residue 0 gives `25 ∣ 10s`, and the residues 1 and 4 make `10s`
exceptional. -/
theorem normalized_bFive_residues {s : ℤ}
    (h25 : ¬ (25 : ℤ) ∣ 2 * (5 * s))
    (hex : ¬ Exceptional125 (2 * (5 * s))) :
    s % 5 = 2 ∨ s % 5 = 3 := by
  have hzero : s % 5 ≠ 0 := by
    intro hz
    obtain ⟨t, rfl⟩ := Int.dvd_iff_emod_eq_zero.mpr hz
    exact h25 ⟨2 * t, by ring⟩
  have hone : s % 5 ≠ 1 := by
    intro h
    apply hex
    have hz : (s - 1) % 5 = 0 := by omega
    obtain ⟨q, hq⟩ := Int.dvd_iff_emod_eq_zero.mpr hz
    refine ⟨0, 2 * q, 2, Or.inl rfl, ?_⟩
    rw [show s = 5 * q + 1 by omega]
    ring
  have hfour : s % 5 ≠ 4 := by
    intro h
    apply hex
    have hz : (s - 4) % 5 = 0 := by omega
    obtain ⟨q, hq⟩ := Int.dvd_iff_emod_eq_zero.mpr hz
    refine ⟨0, 2 * q + 1, 3, Or.inr rfl, ?_⟩
    rw [show s = 5 * q + 4 by omega]
    ring
  have hlo := Int.emod_nonneg s (by norm_num : (5 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos s (by norm_num : (0 : ℤ) < 5)
  omega

/-- For `n > 0`, `BOneRootData n` gives a Mordell datum for `2n` that meets
the conditions of `NormalizedParameterConstruction`. -/
theorem BOneRootData.to_conditions {n : ℤ} (hn : 0 < n)
    (R : BOneRootData n) :
    ∃ d : Datum (2 * n), 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue := by
  let d := oddBOneDatum n R.c R.p R.L R.r R.k R.E R.A
    R.p_eq R.root_eq R.L_eq R.r_eq R.c_ne
  refine ⟨d, ?_⟩
  exact oddBOneDatum_conditions n R.c R.p R.L R.r R.k R.E R.A
    R.p_eq R.root_eq R.L_eq R.r_eq R.c_ne hn R.p_pos R.E_mod R.c_odd

/-- For `s > 0`, `BFiveRootData s` gives a Mordell datum for `10s` that
meets the conditions of `NormalizedParameterConstruction`. -/
theorem BFiveRootData.to_conditions {s : ℤ} (hs : 0 < s)
    (R : BFiveRootData s) :
    ∃ d : Datum (2 * (5 * s)), 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue := by
  let d := oddBFiveDatum s R.c R.P R.d R.r R.k R.E R.v
    R.P_eq R.root_eq R.d_eq R.r_eq R.c_ne
  refine ⟨d, ?_⟩
  exact oddBFiveDatum_conditions s R.c R.P R.d R.r R.k R.E R.v
    R.P_eq R.root_eq R.d_eq R.r_eq R.c_ne hs R.P_pos R.E_mod R.c_odd

/-- The statement that every `n > 0` with `n ≡ 3 (mod 4)` and `5 ∤ n` has
`BOneRootData n`. -/
def BOneRootExistence : Prop :=
  ∀ n : ℤ, 0 < n → n % 4 = 3 → ¬ (5 : ℤ) ∣ n →
    Nonempty (BOneRootData n)

/-- The statement that every `s > 0` with `5s ≡ 3 (mod 4)`, such that `10s`
is nonexceptional and not divisible by 25, has `BFiveRootData s`. The
prime-progression rows need `25 ∤ 10s`; `regular125Sufficiency_of_mordell`
removes this condition by descent. -/
def NormalizedBFiveRootExistence : Prop :=
  ∀ s : ℤ, 0 < s → (5 * s) % 4 = 3 →
    ¬ (25 : ℤ) ∣ 2 * (5 * s) → ¬ Exceptional125 (2 * (5 * s)) → Nonempty (BFiveRootData s)

/-- Every `n > 0` with `n ≡ 3 (mod 4)` and `5 ∤ n` has `BOneRootData n`, by
Dirichlet's theorem and reciprocity. -/
theorem bOneRootExistence : BOneRootExistence := by
  intro n hn hnmod h5
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) :=
    ⟨n.toNat, by simp [Int.toNat_of_nonneg (le_of_lt hn)]⟩
  apply bOneRootData_exists_nat (by exact_mod_cast hnmod)
  intro hz
  apply h5
  apply Int.dvd_iff_emod_eq_zero.mpr
  exact_mod_cast hz

/-- `NormalizedBFiveRootExistence` holds. Only normalized inputs are needed,
since `regular125Sufficiency_of_mordell` removes factors 25 by descent. -/
theorem normalizedBFiveRootExistence : NormalizedBFiveRootExistence := by
  intro s hs hsmod h25 hex
  have hs4 : s % 4 = 3 := by
    simpa only [Int.mul_emod, show (5 : ℤ) % 4 = 1 by norm_num,
      one_mul, Int.emod_emod] using hsmod
  have hres := normalized_bFive_residues h25 hex
  obtain ⟨S, rfl⟩ : ∃ S : ℕ, s = (S : ℤ) :=
    ⟨s.toNat, by simp [Int.toNat_of_nonneg (le_of_lt hs)]⟩
  apply bFiveRootData_exists_nat (by exact_mod_cast hs4)
  exact_mod_cast hres

/-- `BOneRootExistence` implies the case `n ≡ 3 (mod 4)`, `5 ∤ n` of the
parameter construction. -/
theorem evenThreeModFourUnitArithmetic_of_roots
    (hroot : BOneRootExistence) : EvenThreeModFourUnitArithmetic := by
  intro n hn _ _ _ hnmod h5
  obtain ⟨R⟩ := hroot n hn hnmod h5
  exact R.to_conditions hn

/-- `NormalizedBFiveRootExistence` implies the case `n ≡ 3 (mod 4)`, `5 ∣ n`
of the parameter construction. -/
theorem evenThreeModFourFiveArithmetic_of_roots
    (hroot : NormalizedBFiveRootExistence) : EvenThreeModFourFiveArithmetic := by
  intro n hn h25 _ hex hnmod h5
  obtain ⟨s, rfl⟩ := h5
  have hs : 0 < s := by omega
  obtain ⟨R⟩ := hroot s hs hnmod h25 hex
  exact R.to_conditions hs

/-! ## Assembly of the parameter construction -/

/-- The four cases of the parameter construction cover every normalized
input, so together they give `NormalizedParameterConstruction`. -/
theorem normalizedParameterConstruction_of_cases
    (hodd : OddParameterArithmetic)
    (hone : EvenOneModFourArithmetic)
    (hthreeUnit : EvenThreeModFourUnitArithmetic)
    (hthreeFive : EvenThreeModFourFiveArithmetic) :
    NormalizedParameterConstruction := by
  intro m hm h25 h4 hex
  by_cases h2 : (2 : ℤ) ∣ m
  · obtain ⟨n, rfl⟩ := h2
    have hn : 0 < n := by omega
    have hn2 : ¬ (2 : ℤ) ∣ n := by
      rintro ⟨k, rfl⟩
      apply h4
      exact ⟨k, by ring⟩
    have hnmod : n % 4 = 1 ∨ n % 4 = 3 := by
      have hlo : 0 ≤ n % 4 := Int.emod_nonneg _ (by norm_num)
      have hhi : n % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
      generalize hr : n % 4 = r at hlo hhi ⊢
      interval_cases r
      · exfalso
        apply hn2
        apply Int.dvd_iff_emod_eq_zero.mpr
        omega
      · exact Or.inl rfl
      · exfalso
        apply hn2
        apply Int.dvd_iff_emod_eq_zero.mpr
        omega
      · exact Or.inr rfl
    rcases hnmod with hnmod | hnmod
    · exact hone n hn h25 h4 hex hnmod
    · by_cases h5 : (5 : ℤ) ∣ n
      · exact hthreeFive n hn h25 h4 hex hnmod h5
      · exact hthreeUnit n hn h25 h4 hex hnmod h5
  · exact hodd m hm h25 h4 hex h2

/-- `NormalizedParameterConstruction` from the odd case, the case
`n ≡ 1 (mod 4)`, and the two root statements for `n ≡ 3 (mod 4)`. -/
theorem normalizedParameterConstruction_of_root_inputs
    (hodd : OddParameterArithmetic)
    (hone : EvenOneModFourArithmetic)
    (hBOne : BOneRootExistence)
    (hBFive : NormalizedBFiveRootExistence) : NormalizedParameterConstruction := by
  exact normalizedParameterConstruction_of_cases hodd hone
    (evenThreeModFourUnitArithmetic_of_roots hBOne)
    (evenThreeModFourFiveArithmetic_of_roots hBFive)

/-- `NormalizedParameterConstruction` from the odd case and the case
`n ≡ 1 (mod 4)`; the two cases `n ≡ 3 (mod 4)` are proven above. -/
theorem normalizedParameterConstruction_of_two_arithmetic_inputs
    (hodd : OddParameterArithmetic) (hone : EvenOneModFourArithmetic) :
    NormalizedParameterConstruction :=
  normalizedParameterConstruction_of_root_inputs hodd hone
    bOneRootExistence normalizedBFiveRootExistence

/-- The parameter construction and the classification at determinant 10
give a representation by `⟨1,2,5⟩` of every positive nonexceptional `m`
divisible by neither 4 nor 25. The separator `cxx ≡ 6 (mod 16)` excludes
`RepresentsQ2` and `RepresentsQ3`, and the odd value excludes
`RepresentsQ4`. -/
theorem normalized_sufficiency_of_mordell
    (hparam : NormalizedParameterConstruction)
    (hclass : DeterminantTenClassification) :
    ∀ m : ℤ, 0 < m → ¬ (25 : ℤ) ∣ m → ¬ (4 : ℤ) ∣ m →
      ¬ Exceptional125 m →
      Represents125 m := by
  intro m hm h25 h4 hex
  obtain ⟨d, hda, hcxx, hodd⟩ := hparam m hm h25 h4 hex
  rcases hclass d hm hda with hq1 | hq2 | hq3 | hq4
  · exact (hq1 m).1 d.represents_input
  · exfalso
    exact q2_not_six_mod_sixteen d.cxx hcxx ((hq2 d.cxx).1 d.represents_cxx)
  · exfalso
    exact q3_not_six_mod_sixteen d.cxx hcxx ((hq3 d.cxx).1 d.represents_cxx)
  · obtain ⟨r, hr, hro⟩ := hodd
    have hre : r % 2 = 0 := q4_even ((hq4 r).1 hr)
    omega

/-! ## Removing the normalization -/

/-- If `⟨1,2,5⟩` represents `n`, it represents `25n`: multiply every
coordinate by 5. -/
theorem represents125_mul_twentyfive {n : ℤ} (hn : Represents125 n) :
    Represents125 (25 * n) := by
  have h := RegularReductions.diagonal_square_scale 1 2 5 n 5
    (by simpa only [Represents125, one_mul] using hn)
  simpa only [Represents125, one_mul, show (5 : ℤ) ^ 2 = 25 by norm_num] using h

/-- If `⟨1,2,5⟩` represents `n`, it represents `4n`: double every
coordinate. -/
theorem represents125_mul_four {n : ℤ} (hn : Represents125 n) :
    Represents125 (4 * n) := by
  have h := RegularReductions.diagonal_square_scale 1 2 5 n 2
    (by simpa only [Represents125, one_mul] using hn)
  simpa only [Represents125, one_mul, show (2 : ℤ) ^ 2 = 4 by norm_num] using h

/-- The exceptional set of `⟨1,2,5⟩` is closed under multiplication
by 25. -/
theorem exceptional125_mul_twentyfive {n : ℤ} (hn : Exceptional125 n) :
    Exceptional125 (25 * n) := by
  rcases hn with ⟨a, b, r, hr, rfl⟩
  refine ⟨a + 1, b, r, hr, ?_⟩
  rw [pow_succ]
  ring

/-- The exceptional set of `⟨1,2,5⟩` is closed under multiplication by 4;
the residues `r = 2` and `r = 3` are interchanged. -/
theorem exceptional125_mul_four {n : ℤ} (hn : Exceptional125 n) :
    Exceptional125 (4 * n) := by
  rcases hn with ⟨a, b, r, hr, rfl⟩
  rcases hr with rfl | rfl
  · refine ⟨a, 4 * b + 1, 3, Or.inr rfl, ?_⟩
    ring
  · refine ⟨a, 4 * b + 2, 2, Or.inl rfl, ?_⟩
    ring

/-- The parameter construction and the classification at determinant 10
imply `Regular125Sufficiency`. Strong induction removes the factors 25
and 4. -/
theorem regular125Sufficiency_of_mordell
    (hparam : NormalizedParameterConstruction)
    (hclass : DeterminantTenClassification) : Regular125Sufficiency := by
  have hnorm := normalized_sufficiency_of_mordell hparam hclass
  intro n hn hex
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := by
    exact ⟨n.toNat, by simp [Int.toNat_of_nonneg hn]⟩
  have hNat : ∀ N : ℕ, ¬ Exceptional125 (N : ℤ) → Represents125 (N : ℤ) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro hnotN
      by_cases hN : N = 0
      · subst N
        exact ⟨0, 0, 0, by norm_num⟩
      have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      by_cases h25 : 25 ∣ N
      · obtain ⟨K, rfl⟩ := h25
        have hKlt : K < 25 * K := by omega
        have hnotK : ¬ Exceptional125 (K : ℤ) := by
          intro hK
          apply hnotN
          simpa using exceptional125_mul_twentyfive hK
        have hrepK : Represents125 (K : ℤ) := ih K hKlt hnotK
        simpa using represents125_mul_twentyfive hrepK
      · by_cases h4 : 4 ∣ N
        · obtain ⟨K, rfl⟩ := h4
          have hKlt : K < 4 * K := by omega
          have hnotK : ¬ Exceptional125 (K : ℤ) := by
            intro hK
            apply hnotN
            simpa using exceptional125_mul_four hK
          have hrepK : Represents125 (K : ℤ) := ih K hKlt hnotK
          simpa using represents125_mul_four hrepK
        · apply hnorm (N : ℤ)
          · exact_mod_cast hNpos
          · exact_mod_cast h25
          · exact_mod_cast h4
          · exact hnotN
  exact hNat N hex

/-- `Regular125Sufficiency` from the odd case, the case `n ≡ 1 (mod 4)`,
and the classification at determinant 10, which covers all four integral
classes. -/
theorem regular125Sufficiency_of_two_arithmetic_inputs
    (hodd : OddParameterArithmetic) (hone : EvenOneModFourArithmetic)
    (hclass : DeterminantTenClassification) : Regular125Sufficiency :=
  regular125Sufficiency_of_mordell
    (normalizedParameterConstruction_of_two_arithmetic_inputs hodd hone) hclass

/-! ## Even inputs with `n ≡ 1 (mod 4)`

The two constructors below give the parameters for `m = 2n` with
`n ≡ 1 (mod 4)`.

When `5 ∤ n`, take `u = 2` and `q = 3n - 4 + 8nt`. The leading equation then
holds with `E = 6 + 16t`, and the completion equation is `2qc - nk² = 5`.
When `5 ∣ n`, write `n = 5s` and take `u = 10` and `q = 5Q` with
`Q = 3s - 20 + 8st`; the completion equation becomes `2Qc - sk² = 1`.

Dirichlet's theorem and reciprocity supply the primes and square roots
(`evenOneModFourArithmetic`).
-/

/-- The datum `evenDatum` for the case `5 ∤ n`, with `u = 2`,
`q = 3n - 4 + 8nt`, and `E = 6 + 16t`; the leading equation holds
identically. -/
def evenUnitFiveDatum (n t k c : ℤ)
    (hdet : 2 * (3 * n - 4 + 8 * n * t) * c - n * k ^ 2 = 5) :
    Datum (2 * n) :=
  evenDatum n (3 * n - 4 + 8 * n * t) 2 k c (6 + 16 * t)
    (by ring) hdet

/-- If `q > 0` and `c` is odd, then `evenUnitFiveDatum` meets the conditions
of `NormalizedParameterConstruction`. -/
theorem evenUnitFiveDatum_conditions (n t k c : ℤ)
    (hdet : 2 * (3 * n - 4 + 8 * n * t) * c - n * k ^ 2 = 5)
    (hq : 0 < 3 * n - 4 + 8 * n * t) (hc : c % 2 = 1) :
    0 < (evenUnitFiveDatum n t k c hdet).a ∧
      (evenUnitFiveDatum n t k c hdet).cxx % 16 = 6 ∧
      (evenUnitFiveDatum n t k c hdet).HasOddValue := by
  apply evenDatum_conditions
  · nlinarith
  · norm_num [Int.add_emod, Int.mul_emod]
  · exact hc

/-- The datum `evenDatum` for the case `n = 5s`, with `u = 10`, `q = 5Q`,
`Q = 3s - 20 + 8st`, and `E = 6 + 16t`. The completion equation is divided
by 5. -/
def evenFiveDatum (s t k c : ℤ)
    (hdet : 2 * (3 * s - 20 + 8 * s * t) * c - s * k ^ 2 = 1) :
    Datum (2 * (5 * s)) :=
  evenDatum (5 * s) (5 * (3 * s - 20 + 8 * s * t)) 10 k c
    (6 + 16 * t) (by ring) (by nlinarith)

/-- If `Q > 0` and `c` is odd, then `evenFiveDatum` meets the conditions of
`NormalizedParameterConstruction`. -/
theorem evenFiveDatum_conditions (s t k c : ℤ)
    (hdet : 2 * (3 * s - 20 + 8 * s * t) * c - s * k ^ 2 = 1)
    (hQ : 0 < 3 * s - 20 + 8 * s * t) (hc : c % 2 = 1) :
    0 < (evenFiveDatum s t k c hdet).a ∧
      (evenFiveDatum s t k c hdet).cxx % 16 = 6 ∧
      (evenFiveDatum s t k c hdet).HasOddValue := by
  apply evenDatum_conditions
  · nlinarith
  · norm_num [Int.add_emod, Int.mul_emod]
  · exact hc

/-! ## Roots for even inputs with `n ≡ 1 (mod 4)` -/

/-- For odd `q`, a solution of `q ∣ D x² + e` can be chosen odd. -/
theorem exists_odd_root {q D e x : ℤ} (hq : q % 2 = 1)
    (hx : q ∣ D * x ^ 2 + e) :
    ∃ k : ℤ, k % 2 = 1 ∧ q ∣ D * k ^ 2 + e := by
  let j := 1 - x
  obtain ⟨v, hv⟩ := hx
  refine ⟨x + q * j, ?_, v + D * (2 * x * j + q * j ^ 2), ?_⟩
  · dsimp [j]
    norm_num [Int.add_emod, Int.sub_emod, Int.mul_emod, hq]
    omega
  · calc
      D * (x + q * j) ^ 2 + e =
          (D * x ^ 2 + e) + q * (D * (2 * x * j + q * j ^ 2)) := by ring
      _ = q * (v + D * (2 * x * j + q * j ^ 2)) := by rw [hv]; ring

/-- If `n ≡ 1 (mod 4)`, `e ≡ 1 (mod 4)`, `q` and `k` are odd, and
`q ∣ nk² + e`, then `2qc - nk² = e` for some odd `c`. Both even constructors
use this, with `e = 5` and `e = 1`. -/
theorem exists_odd_half_completion {n q e k : ℤ}
    (hn : n % 4 = 1) (hq : q % 2 = 1) (he : e % 4 = 1)
    (hk : k % 2 = 1) (hroot : q ∣ n * k ^ 2 + e) :
    ∃ c : ℤ, 2 * q * c - n * k ^ 2 = e ∧ c % 2 = 1 := by
  obtain ⟨v, hv⟩ := hroot
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by omega
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  have hm := congrArg (fun z : ℤ => z % 4) hv
  have hv4 : v % 4 = 2 := by
    rcases hk4 with hk4 | hk4 <;> rcases hq4 with hq4 | hq4 <;>
      norm_num [pow_two, Int.add_emod, Int.mul_emod, hn, he, hk4, hq4] at hm <;>
      omega
  have hv2 : v % 2 = 0 := by omega
  obtain ⟨c, hc⟩ := Int.dvd_iff_emod_eq_zero.mpr hv2
  refine ⟨c, ?_, ?_⟩
  · rw [hc] at hv
    nlinarith
  · rw [hc] at hv4
    omega

/-- Reciprocity for even inputs with `5 ∤ n`: if `n ≡ 1 (mod 4)`,
`q ≡ 3 (mod 4)`, `q ≡ 2 (mod 5)`, and `q ≡ -4 (mod n)`, then
`(-5n/q) = 1`. -/
theorem evenUnit_jacobi_reciprocity {n q : ℕ}
    (hn : n % 4 = 1) (hq : q % 4 = 3) (hq5 : q % 5 = 2)
    (hqn : (q : ℤ) ≡ -4 [ZMOD (n : ℤ)]) :
    jacobiSym (-(5 * (n : ℤ))) q = 1 := by
  have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hfive : jacobiSym (-5) q = 1 := by
    have hq5z : (q : ℤ) % 5 = 2 := by exact_mod_cast hq5
    rw [jacobi_neg_five_of_three_mod_four hq, jacobiSym.mod_left]
    norm_num [hq5z]
  have hnq : jacobiSym (n : ℤ) q = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four hn hqodd,
      jacobiSym.mod_left' hqn, jacobiSym.neg _ hnodd,
      ZMod.χ₄_nat_one_mod_four hn, one_mul, jacobiSym.at_four hnodd]
  rw [show -(5 * (n : ℤ)) = (-5) * (n : ℤ) by ring,
    jacobiSym.mul_left, hfive, hnq]
  norm_num

/-- Reciprocity for even inputs `2n` with `n = 5s`: if `s ≡ 1 (mod 4)`,
`s ≡ 2, 3 (mod 5)`, `q ≡ 3 (mod 4)`, and `q ≡ -20 (mod s)`, then
`(-s/q) = 1`. Nonexceptionality gives the residues of `s` modulo 5. -/
theorem evenFive_jacobi_reciprocity {s q : ℕ}
    (hs : s % 4 = 1) (hq : q % 4 = 3)
    (hs5 : s % 5 = 2 ∨ s % 5 = 3)
    (hqs : (q : ℤ) ≡ -20 [ZMOD (s : ℤ)]) :
    jacobiSym (-(s : ℤ)) q = 1 := by
  have hsodd : Odd s := Nat.odd_iff.mpr (by omega)
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hsval : jacobiSym (-20) s = -1 := by
    rw [show (-20 : ℤ) = -(5 * 4) by norm_num,
      jacobiSym.neg _ hsodd, ZMod.χ₄_nat_one_mod_four hs, one_mul,
      jacobiSym.mul_left, jacobiSym.at_four hsodd, mul_one]
    change jacobiSym ((5 : ℕ) : ℤ) s = -1
    rw [jacobiSym.quadratic_reciprocity_one_mod_four
        (by norm_num : (5 : ℕ) % 4 = 1) hsodd,
      jacobiSym.mod_left]
    rcases hs5 with hs5 | hs5
    · have hs5z : (s : ℤ) % 5 = 2 := by exact_mod_cast hs5
      norm_num [hs5z]
    · have hs5z : (s : ℤ) % 5 = 3 := by exact_mod_cast hs5
      norm_num [hs5z]
  rw [jacobiSym.neg _ hqodd, ZMod.χ₄_nat_three_mod_four hq,
    jacobiSym.quadratic_reciprocity_one_mod_four hs hqodd,
    jacobiSym.mod_left' hqs, hsval]
  norm_num

/-- Let `n ≡ 1 (mod 4)`. A prime `q = 3n - 4 + 8nt` with `q ≡ 2 (mod 5)`
gives a Mordell datum for `2n` that meets the conditions of
`NormalizedParameterConstruction`. -/
theorem evenUnit_conditions_of_prime {n q : ℕ} [Fact q.Prime] {t : ℤ}
    (hn : n % 4 = 1) (hq5 : q % 5 = 2)
    (hqt : (q : ℤ) = 3 * n - 4 + 8 * n * t) :
    ∃ d : Datum (2 * (n : ℤ)), 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue := by
  have hq4z : (q : ℤ) % 4 = 3 := by
    have hnz : (n : ℤ) % 4 = 1 := by exact_mod_cast hn
    rw [hqt]
    norm_num [Int.add_emod, Int.sub_emod, Int.mul_emod, hnz]
  have hq4 : q % 4 = 3 := by exact_mod_cast hq4z
  have hqn : (q : ℤ) ≡ -4 [ZMOD (n : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(3 + 8 * t), ?_⟩
    rw [hqt]
    ring
  have hleg : legendreSym q (-((5 * n : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using evenUnit_jacobi_reciprocity hn hq4 hq5 hqn
  obtain ⟨u, x, hux⟩ := MordellRegularity.exists_binary_unit_completion_of_legendre
    (nonzero_of_neg_legendre_one hleg) hleg
  have hroot : (q : ℤ) ∣ (n : ℤ) * (5 * x) ^ 2 + 5 := by
    refine ⟨5 * u, ?_⟩
    push_cast at hux
    nlinarith
  obtain ⟨k, hk, hrootk⟩ := exists_odd_root (by omega : (q : ℤ) % 2 = 1) hroot
  obtain ⟨c, hdet, hc⟩ := exists_odd_half_completion (by exact_mod_cast hn)
    (by omega : (q : ℤ) % 2 = 1) (by norm_num : (5 : ℤ) % 4 = 1) hk hrootk
  have hdet' : 2 * (3 * (n : ℤ) - 4 + 8 * n * t) * c - n * k ^ 2 = 5 := by
    simpa only [hqt] using hdet
  refine ⟨evenUnitFiveDatum n t k c hdet', ?_⟩
  apply evenUnitFiveDatum_conditions
  · rw [← hqt]
    exact_mod_cast (Fact.out : q.Prime).pos
  · exact hc

/-- Coprimality for the progressions of even inputs with `n ≡ 1 (mod 4)`:
if `R + b = Kn` with `b = 4` or `b = 20`, `R` is odd, and `R ≡ 2 (mod 5)`,
then `R` is prime to `40n`. -/
theorem evenOneProgression_coprime (n R K b : ℕ)
    (hlin : R + b = K * n) (hodd : R % 2 = 1) (hfive : R % 5 = 2)
    (hb : b = 4 ∨ b = 20) : R.Coprime (40 * n) := by
  have h2 : (2 : ℕ).Coprime R := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro hd
    obtain ⟨k, hk⟩ := hd
    omega
  have h5 : (5 : ℕ).Coprime R := by
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
    intro hd
    obtain ⟨k, hk⟩ := hd
    omega
  have h4 : (4 : ℕ).Coprime R := by
    simpa using Nat.Coprime.pow_left 2 h2
  have hbR : b.Coprime R := by
    rcases hb with rfl | rfl
    · exact h4
    · simpa using h4.mul_left h5
  have hsum : (R + b).Coprime R := by
    simpa [Nat.add_comm] using hbR
  have hnR : n.Coprime R := by
    apply Nat.Coprime.of_dvd_left
      (show n ∣ R + b from ⟨K, by simpa [Nat.mul_comm] using hlin⟩)
    exact hsum
  have h8 : R.Coprime 8 := by
    simpa using Nat.Coprime.pow_right 3 h2.symm
  have hall := (h8.mul_right h5.symm).mul_right hnR.symm
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hall

/-- Dirichlet's theorem for one row of the progressions with
`n ≡ 1 (mod 4)`: some prime `q ≡ 2 (mod 5)` has the form
`q = 3n - b + 8nt`. -/
theorem exists_evenOne_prime_row (n R t0 b : ℕ) (hn : 0 < n)
    (hlin : R + b = (3 + 8 * t0) * n)
    (hodd : R % 2 = 1) (hfive : R % 5 = 2) (hb : b = 4 ∨ b = 20) :
    ∃ q : ℕ, ∃ t : ℤ, q.Prime ∧ q % 5 = 2 ∧
      (q : ℤ) = 3 * n - b + 8 * n * t := by
  obtain ⟨q, k, hq, hqk⟩ :=
    MordellRegularity.exists_auxiliary_prime_eq_add_mul (40 * n) R (by omega)
      (evenOneProgression_coprime n R (3 + 8 * t0) b hlin hodd hfive hb)
  have hlinZ : (R : ℤ) + b = (3 + 8 * (t0 : ℤ)) * n := by exact_mod_cast hlin
  have hqkZ : (q : ℤ) = R + 40 * n * (k : ℤ) := by exact_mod_cast hqk
  refine ⟨q, (t0 : ℤ) + 5 * k, hq, ?_, ?_⟩
  · rw [hqk]
    norm_num [Nat.add_mod, Nat.mul_mod, hfive]
  · nlinarith

/-- For `n ≡ 1 (mod 4)` with `5 ∤ n`, some prime `q ≡ 2 (mod 5)` has the
form `q = 3n - 4 + 8nt`. -/
theorem exists_evenUnit_prime (n : ℕ) (hn : n % 4 = 1) (h5 : n % 5 ≠ 0) :
    ∃ q : ℕ, ∃ t : ℤ, q.Prime ∧ q % 5 = 2 ∧
      (q : ℤ) = 3 * n - 4 + 8 * n * t := by
  have hpos : 0 < n := by omega
  have hres : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hres with hres | hres | hres | hres
  · exact exists_evenOne_prime_row n (51 * n - 4) 6 4 hpos
      (by omega) (by omega) (by omega) (Or.inl rfl)
  · exact exists_evenOne_prime_row n (43 * n - 4) 5 4 hpos
      (by omega) (by omega) (by omega) (Or.inl rfl)
  · exact exists_evenOne_prime_row n (27 * n - 4) 3 4 hpos
      (by omega) (by omega) (by omega) (Or.inl rfl)
  · exact exists_evenOne_prime_row n (59 * n - 4) 7 4 hpos
      (by omega) (by omega) (by omega) (Or.inl rfl)

/-- For `s ≡ 1 (mod 4)` with `s ≡ 2, 3 (mod 5)`, some prime `q ≡ 2 (mod 5)`
has the form `q = 3s - 20 + 8st`. -/
theorem exists_evenFive_prime (s : ℕ) (hs : s % 4 = 1)
    (h5 : s % 5 = 2 ∨ s % 5 = 3) :
    ∃ q : ℕ, ∃ t : ℤ, q.Prime ∧ q % 5 = 2 ∧
      (q : ℤ) = 3 * s - 20 + 8 * s * t := by
  have hpos : 0 < s := by omega
  rcases h5 with h5 | h5
  · exact exists_evenOne_prime_row s (51 * s - 20) 6 20 hpos
      (by omega) (by omega) (by omega) (Or.inr rfl)
  · exact exists_evenOne_prime_row s (59 * s - 20) 7 20 hpos
      (by omega) (by omega) (by omega) (Or.inr rfl)

/-- Let `s ≡ 1 (mod 4)` and `s ≡ 2, 3 (mod 5)`. A prime
`q = 3s - 20 + 8st` gives a Mordell datum for `10s` that meets the conditions
of `NormalizedParameterConstruction`. -/
theorem evenFive_conditions_of_prime {s q : ℕ} [Fact q.Prime] {t : ℤ}
    (hs : s % 4 = 1) (hs5 : s % 5 = 2 ∨ s % 5 = 3)
    (hqt : (q : ℤ) = 3 * s - 20 + 8 * s * t) :
    ∃ d : Datum (2 * (5 * (s : ℤ))), 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue := by
  have hq4z : (q : ℤ) % 4 = 3 := by
    have hsz : (s : ℤ) % 4 = 1 := by exact_mod_cast hs
    rw [hqt]
    norm_num [Int.add_emod, Int.sub_emod, Int.mul_emod, hsz]
  have hq4 : q % 4 = 3 := by exact_mod_cast hq4z
  have hqs : (q : ℤ) ≡ -20 [ZMOD (s : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(3 + 8 * t), ?_⟩
    rw [hqt]
    ring
  have hleg : legendreSym q (-(s : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    exact evenFive_jacobi_reciprocity hs hq4 hs5 hqs
  obtain ⟨u, x, hux⟩ := MordellRegularity.exists_binary_unit_completion_of_legendre
    (nonzero_of_neg_legendre_one hleg) hleg
  have hroot : (q : ℤ) ∣ (s : ℤ) * x ^ 2 + 1 := ⟨u, by nlinarith⟩
  obtain ⟨k, hk, hrootk⟩ := exists_odd_root (by omega : (q : ℤ) % 2 = 1) hroot
  obtain ⟨c, hdet, hc⟩ := exists_odd_half_completion (by exact_mod_cast hs)
    (by omega : (q : ℤ) % 2 = 1) (by norm_num : (1 : ℤ) % 4 = 1) hk hrootk
  have hdet' : 2 * (3 * (s : ℤ) - 20 + 8 * s * t) * c - s * k ^ 2 = 1 := by
    simpa only [hqt] using hdet
  refine ⟨evenFiveDatum s t k c hdet', ?_⟩
  apply evenFiveDatum_conditions
  · rw [← hqt]
    exact_mod_cast (Fact.out : q.Prime).pos
  · exact hc

/-- The case `n ≡ 1 (mod 4)` of the parameter construction, by Dirichlet's
theorem, quadratic reciprocity, and the odd-root completion. -/
theorem evenOneModFourArithmetic : EvenOneModFourArithmetic := by
  intro n hn h25 _ hex hn4
  by_cases h5 : (5 : ℤ) ∣ n
  · obtain ⟨s, rfl⟩ := h5
    have hs : 0 < s := by omega
    have hs4 : s % 4 = 1 := by
      simpa only [Int.mul_emod, show (5 : ℤ) % 4 = 1 by norm_num,
        one_mul, Int.emod_emod] using hn4
    have hs5 := normalized_bFive_residues h25 hex
    obtain ⟨S, rfl⟩ : ∃ S : ℕ, s = (S : ℤ) :=
      ⟨s.toNat, by simp [Int.toNat_of_nonneg (le_of_lt hs)]⟩
    have hS4 : S % 4 = 1 := by exact_mod_cast hs4
    have hS5 : S % 5 = 2 ∨ S % 5 = 3 := by exact_mod_cast hs5
    obtain ⟨q, t, hq, _, hqt⟩ := exists_evenFive_prime S hS4 hS5
    let _ : Fact q.Prime := ⟨hq⟩
    exact evenFive_conditions_of_prime hS4 hS5 hqt
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) :=
      ⟨n.toNat, by simp [Int.toNat_of_nonneg (le_of_lt hn)]⟩
    have hN4 : N % 4 = 1 := by exact_mod_cast hn4
    have hN5 : N % 5 ≠ 0 := by
      intro hz
      apply h5
      apply Int.dvd_iff_emod_eq_zero.mpr
      exact_mod_cast hz
    obtain ⟨q, t, hq, hq5, hqt⟩ := exists_evenUnit_prime N hN4 hN5
    let _ : Fact q.Prime := ⟨hq⟩
    exact evenUnit_conditions_of_prime hN4 hq5 hqt

/-- `Regular125Sufficiency` from the odd case and the classification at
determinant 10; the even cases are proven above. -/
theorem regular125Sufficiency_of_odd_arithmetic
    (hodd : OddParameterArithmetic) (hclass : DeterminantTenClassification) :
    Regular125Sufficiency :=
  regular125Sufficiency_of_two_arithmetic_inputs hodd evenOneModFourArithmetic hclass

/-! ## Odd inputs

For odd `m` with `5 ∤ m`, choose a prime `q = (6 + 16t)m - 1` with
`q ≡ 2 (mod 5)`. For `m = 5s`, choose a prime `q = (6 + 16t)s - 5` with
`q ≡ 2 (mod 5)`; the normalized nonexceptional classes are
`s ≡ 1, 4 (mod 5)`. Jacobi reciprocity applies to `m` or `s` directly, so the
proof needs neither a factorization nor a squarefree reduction of the input.
-/

/-- The Mordell datum with `B = 0`, `h = mk`, and `b = mc`, given
`A² + a = mE` and `ac - mk² = 10`. It serves the odd inputs. -/
def oddInputDatum (m A a k c E : ℤ)
    (hlead : A ^ 2 + a = m * E) (hdet : a * c - m * k ^ 2 = 10) :
    Datum m where
  A := A
  B := 0
  a := a
  h := m * k
  b := m * c
  cxx := E
  cxy := k
  cyy := c
  xx_eq := hlead
  xy_eq := by ring
  yy_eq := by ring
  determinant_eq := by
    calc
      a * (m * c) - (m * k) ^ 2 = m * (a * c - m * k ^ 2) := by ring
      _ = 10 * m := by rw [hdet]; ring

/-- If `a > 0`, `E ≡ 6 (mod 16)`, and `m` is odd, then `oddInputDatum` meets the
conditions of `NormalizedParameterConstruction`; the odd value is `m`. -/
theorem oddInputDatum_conditions (m A a k c E : ℤ)
    (hlead : A ^ 2 + a = m * E) (hdet : a * c - m * k ^ 2 = 10)
    (ha : 0 < a) (hE : E % 16 = 6) (hm : m % 2 = 1) :
    0 < (oddInputDatum m A a k c E hlead hdet).a ∧
      (oddInputDatum m A a k c E hlead hdet).cxx % 16 = 6 ∧
      (oddInputDatum m A a k c E hlead hdet).HasOddValue := by
  refine ⟨ha, hE, m, ?_, hm⟩
  exact (oddInputDatum m A a k c E hlead hdet).represents_input

/-- Reciprocity for odd `m` with `5 ∤ m`: if `q ≡ 1 (mod 4)`,
`q ≡ 2 (mod 5)`, `q ≡ 6m + 7 (mod 8)`, and `q ≡ -1 (mod m)`, then
`(-10m/q) = 1`. The signs of `(2/q)`, `(5/q)`, and `(m/q)` cancel. -/
theorem oddUnit_jacobi_reciprocity {m q : ℕ}
    (hm : m % 2 = 1) (hq4 : q % 4 = 1) (hq5 : q % 5 = 2)
    (hq8 : q % 8 = (6 * m + 7) % 8)
    (hqm : (q : ℤ) ≡ -1 [ZMOD (m : ℤ)]) :
    jacobiSym (-(10 * (m : ℤ))) q = 1 := by
  have hmo : Odd m := Nat.odd_iff.mpr hm
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hmq : jacobiSym (m : ℤ) q = ZMod.χ₄ m := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hmo hq4,
      jacobiSym.mod_left' hqm, jacobiSym.at_neg_one hmo]
  have hfive : jacobiSym 5 q = -1 := by
    change jacobiSym ((5 : ℕ) : ℤ) q = -1
    have hq5z : (q : ℤ) % 5 = 2 := by exact_mod_cast hq5
    rw [jacobiSym.quadratic_reciprocity_one_mod_four
      (by norm_num : (5 : ℕ) % 4 = 1) hqo, jacobiSym.mod_left]
    norm_num [hq5z]
  have hsign : ZMod.χ₈ q * ZMod.χ₄ m = (-1 : ℤ) := by
    have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hm4 with hm4 | hm4
    · have hq8' : q % 8 = 5 := by omega
      rw [ZMod.χ₄_nat_one_mod_four hm4]
      have hq2 : q % 2 ≠ 0 := by omega
      have hchi8 : ZMod.χ₈ q = -1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        simp [hq2, hq8']
      rw [hchi8]
      norm_num
    · have hq8' : q % 8 = 1 := by omega
      rw [ZMod.χ₄_nat_three_mod_four hm4]
      have hq2 : q % 2 ≠ 0 := by omega
      have hchi8 : ZMod.χ₈ q = 1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        simp [hq2, hq8']
      rw [hchi8]
      norm_num
  rw [show -(10 * (m : ℤ)) = -(2 * 5 * (m : ℤ)) by ring,
    jacobiSym.neg _ hqo, ZMod.χ₄_nat_one_mod_four hq4, one_mul,
    jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_two hqo, hfive, hmq]
  nlinarith [hsign]

/-- Reciprocity for `m = 5s`: if `s` is odd, `s ≡ 1, 4 (mod 5)`,
`q ≡ 1 (mod 4)`, `q ≡ 6s + 3 (mod 8)`, and `q ≡ -5 (mod s)`, then
`(-2s/q) = 1`. Reciprocity turns `(s/q)` into `(-5/s)`, and
`(5/s) = (s/5) = 1`. -/
theorem oddFive_jacobi_reciprocity {s q : ℕ}
    (hs : s % 2 = 1) (hq4 : q % 4 = 1)
    (hs5 : s % 5 = 1 ∨ s % 5 = 4)
    (hq8 : q % 8 = (6 * s + 3) % 8)
    (hqs : (q : ℤ) ≡ -5 [ZMOD (s : ℤ)]) :
    jacobiSym (-(2 * (s : ℤ))) q = 1 := by
  have hso : Odd s := Nat.odd_iff.mpr hs
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hfive : jacobiSym 5 s = 1 := by
    change jacobiSym ((5 : ℕ) : ℤ) s = 1
    rw [jacobiSym.quadratic_reciprocity_one_mod_four
      (by norm_num : (5 : ℕ) % 4 = 1) hso, jacobiSym.mod_left]
    rcases hs5 with hs5 | hs5
    · have hs5z : (s : ℤ) % 5 = 1 := by exact_mod_cast hs5
      norm_num [hs5z]
    · have hs5z : (s : ℤ) % 5 = 4 := by exact_mod_cast hs5
      norm_num [hs5z]
  have hsq : jacobiSym (s : ℤ) q = ZMod.χ₄ s := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hso hq4,
      jacobiSym.mod_left' hqs, jacobiSym.neg _ hso, hfive, mul_one]
  have hsign : ZMod.χ₈ q * ZMod.χ₄ s = (1 : ℤ) := by
    have hs4 : s % 4 = 1 ∨ s % 4 = 3 := by omega
    rcases hs4 with hs4 | hs4
    · have hq8' : q % 8 = 1 := by omega
      rw [ZMod.χ₄_nat_one_mod_four hs4]
      have hq2 : q % 2 ≠ 0 := by omega
      have hchi8 : ZMod.χ₈ q = 1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        simp [hq2, hq8']
      rw [hchi8]
      norm_num
    · have hq8' : q % 8 = 5 := by omega
      rw [ZMod.χ₄_nat_three_mod_four hs4]
      have hq2 : q % 2 ≠ 0 := by omega
      have hchi8 : ZMod.χ₈ q = -1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        simp [hq2, hq8']
      rw [hchi8]
      norm_num
  rw [jacobiSym.neg _ hqo, ZMod.χ₄_nat_one_mod_four hq4, one_mul,
    jacobiSym.mul_left, jacobiSym.at_two hqo, hsq]
  exact hsign

/-- Dirichlet's theorem for one row of the odd inputs: for `b = 1` or
`b = 5`, some prime `q ≡ 2 (mod 5)` has the form `q = 6m - b + 16mt`. -/
theorem exists_oddInput_prime_row (m R t0 b : ℕ) (hm : 0 < m)
    (hlin : R + b = (6 + 16 * t0) * m)
    (hodd : R % 2 = 1) (hfive : R % 5 = 2) (hb : b = 1 ∨ b = 5) :
    ∃ q : ℕ, ∃ t : ℤ, q.Prime ∧ q % 5 = 2 ∧
      (q : ℤ) = 6 * m - b + 16 * m * t := by
  have hcop : R.Coprime (160 * m) := by
    rcases hb with rfl | rfl
    · exact progressionResidue_coprime m R (6 + 16 * t0) hlin hodd hfive
    · exact fiveProgressionResidue_coprime m R (6 + 16 * t0) hlin hodd hfive
  obtain ⟨q, k, hq, hqk⟩ := MordellRegularity.exists_auxiliary_prime_eq_add_mul
    (160 * m) R (by omega) hcop
  have hlinZ : (R : ℤ) + b = (6 + 16 * (t0 : ℤ)) * m := by exact_mod_cast hlin
  have hqkZ : (q : ℤ) = R + 160 * m * (k : ℤ) := by exact_mod_cast hqk
  refine ⟨q, (t0 : ℤ) + 10 * k, hq, ?_, ?_⟩
  · rw [hqk]
    norm_num [Nat.add_mod, Nat.mul_mod, hfive]
  · nlinarith

/-- For odd `m` with `5 ∤ m`, some prime `q ≡ 2 (mod 5)` has the form
`q = 6m - 1 + 16mt`. -/
theorem exists_oddUnit_prime (m : ℕ) (hm : m % 2 = 1) (h5 : m % 5 ≠ 0) :
    ∃ q : ℕ, ∃ t : ℤ, q.Prime ∧ q % 5 = 2 ∧
      (q : ℤ) = 6 * m - 1 + 16 * m * t := by
  have hp : 0 < m := by omega
  have hr : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  rcases hr with hr | hr | hr | hr
  · exact exists_oddInput_prime_row m (38 * m - 1) 2 1 hp
      (by omega) (by omega) (by omega) (Or.inl rfl)
  · exact exists_oddInput_prime_row m (54 * m - 1) 3 1 hp
      (by omega) (by omega) (by omega) (Or.inl rfl)
  · exact exists_oddInput_prime_row m (6 * m - 1) 0 1 hp
      (by omega) (by omega) (by omega) (Or.inl rfl)
  · exact exists_oddInput_prime_row m (22 * m - 1) 1 1 hp
      (by omega) (by omega) (by omega) (Or.inl rfl)

/-- For odd `s` with `s ≡ 1, 4 (mod 5)`, some prime `q ≡ 2 (mod 5)` has the form
`q = 6s - 5 + 16st`. -/
theorem exists_oddFive_prime (s : ℕ) (hs : s % 2 = 1)
    (h5 : s % 5 = 1 ∨ s % 5 = 4) :
    ∃ q : ℕ, ∃ t : ℤ, q.Prime ∧ q % 5 = 2 ∧
      (q : ℤ) = 6 * s - 5 + 16 * s * t := by
  have hp : 0 < s := by omega
  rcases h5 with h5 | h5
  · exact exists_oddInput_prime_row s (22 * s - 5) 1 5 hp
      (by omega) (by omega) (by omega) (Or.inr rfl)
  · exact exists_oddInput_prime_row s (38 * s - 5) 2 5 hp
      (by omega) (by omega) (by omega) (Or.inr rfl)

/-- Let `m` be odd. A prime `q = 6m - 1 + 16mt` with `q ≡ 2 (mod 5)` gives a
Mordell datum for `m` that meets the conditions of
`NormalizedParameterConstruction`. -/
theorem oddUnit_conditions_of_prime {m q : ℕ} [Fact q.Prime] {t : ℤ}
    (hm : m % 2 = 1) (hq5 : q % 5 = 2)
    (hqt : (q : ℤ) = 6 * m - 1 + 16 * m * t) :
    ∃ d : Datum (m : ℤ), 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue := by
  have hmz : (m : ℤ) % 2 = 1 := by exact_mod_cast hm
  have hq8z : (q : ℤ) % 8 = (6 * (m : ℤ) - 1) % 8 := by
    rw [hqt]
    simp [Int.add_emod, Int.mul_emod]
  have hq8 : q % 8 = (6 * m + 7) % 8 := by omega
  have hq4 : q % 4 = 1 := by omega
  have hqm : (q : ℤ) ≡ -1 [ZMOD (m : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(6 + 16 * t), ?_⟩
    rw [hqt]
    ring
  have hleg : legendreSym q (-((10 * m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      oddUnit_jacobi_reciprocity hm hq4 hq5 hq8 hqm
  obtain ⟨u, x, hux⟩ := MordellRegularity.exists_binary_unit_completion_of_legendre
    (nonzero_of_neg_legendre_one hleg) hleg
  push_cast at hux
  have hdet : (q : ℤ) * (10 * u) - m * (10 * x) ^ 2 = 10 := by nlinarith
  have hlead : (1 : ℤ) ^ 2 + q = m * (6 + 16 * t) := by rw [hqt]; ring
  refine ⟨oddInputDatum m 1 q (10 * x) (10 * u) (6 + 16 * t) hlead hdet, ?_⟩
  apply oddInputDatum_conditions
  · exact_mod_cast (Fact.out : q.Prime).pos
  · omega
  · exact hmz

/-- Let `s` be odd with `s ≡ 1, 4 (mod 5)`. A prime `q = 6s - 5 + 16st` gives a
Mordell datum for `5s` that meets the conditions of
`NormalizedParameterConstruction`. -/
theorem oddFive_conditions_of_prime {s q : ℕ} [Fact q.Prime] {t : ℤ}
    (hs : s % 2 = 1) (hs5 : s % 5 = 1 ∨ s % 5 = 4)
    (hqt : (q : ℤ) = 6 * s - 5 + 16 * s * t) :
    ∃ d : Datum (5 * (s : ℤ)), 0 < d.a ∧ d.cxx % 16 = 6 ∧ d.HasOddValue := by
  have hsz : (s : ℤ) % 2 = 1 := by exact_mod_cast hs
  have hq8z : (q : ℤ) % 8 = (6 * (s : ℤ) - 5) % 8 := by
    rw [hqt]
    simp [Int.add_emod, Int.mul_emod]
  have hq8 : q % 8 = (6 * s + 3) % 8 := by omega
  have hq4 : q % 4 = 1 := by omega
  have hqs : (q : ℤ) ≡ -5 [ZMOD (s : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(6 + 16 * t), ?_⟩
    rw [hqt]
    ring
  have hleg : legendreSym q (-((2 * s : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      oddFive_jacobi_reciprocity hs hq4 hs5 hq8 hqs
  obtain ⟨u, x, hux⟩ := MordellRegularity.exists_binary_unit_completion_of_legendre
    (nonzero_of_neg_legendre_one hleg) hleg
  push_cast at hux
  have hdet : (5 * (q : ℤ)) * (2 * u) - (5 * s) * (2 * x) ^ 2 = 10 := by
    nlinarith
  have hlead : (5 : ℤ) ^ 2 + 5 * q = (5 * s) * (6 + 16 * t) := by
    rw [hqt]; ring
  refine ⟨oddInputDatum (5 * s) 5 (5 * q) (2 * x) (2 * u)
    (6 + 16 * t) hlead hdet, ?_⟩
  apply oddInputDatum_conditions
  · have : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    positivity
  · omega
  · omega

/-- If `25 ∤ 5s` and `5s` is not exceptional, then `s ≡ 1, 4 (mod 5)`, a
nonzero square modulo 5. -/
theorem normalized_oddFive_residues {s : ℤ}
    (h25 : ¬ (25 : ℤ) ∣ 5 * s) (hex : ¬ Exceptional125 (5 * s)) :
    s % 5 = 1 ∨ s % 5 = 4 := by
  have hz : s % 5 ≠ 0 := by
    intro h
    obtain ⟨k, rfl⟩ := Int.dvd_iff_emod_eq_zero.mpr h
    exact h25 ⟨k, by ring⟩
  have htwo : s % 5 ≠ 2 := by
    intro h
    apply hex
    have hz : (s - 2) % 5 = 0 := by omega
    obtain ⟨q, hq⟩ := Int.dvd_iff_emod_eq_zero.mpr hz
    refine ⟨0, q, 2, Or.inl rfl, ?_⟩
    rw [show s = 5 * q + 2 by omega]
    ring
  have hthree : s % 5 ≠ 3 := by
    intro h
    apply hex
    have hz : (s - 3) % 5 = 0 := by omega
    obtain ⟨q, hq⟩ := Int.dvd_iff_emod_eq_zero.mpr hz
    refine ⟨0, q, 3, Or.inr rfl, ?_⟩
    rw [show s = 5 * q + 3 by omega]
    ring
  have hlo := Int.emod_nonneg s (by norm_num : (5 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos s (by norm_num : (0 : ℤ) < 5)
  omega

/-- The odd case of the parameter construction, by Dirichlet's theorem and
Jacobi reciprocity. -/
theorem oddParameterArithmetic : OddParameterArithmetic := by
  intro m hm h25 _ hex h2
  have hm2 : m % 2 = 1 := by
    have : m % 2 ≠ 0 := fun h ↦ h2 (Int.dvd_iff_emod_eq_zero.mpr h)
    omega
  by_cases h5 : (5 : ℤ) ∣ m
  · obtain ⟨s, rfl⟩ := h5
    have hs : 0 < s := by omega
    have hs2 : s % 2 = 1 := by omega
    have hs5 := normalized_oddFive_residues h25 hex
    obtain ⟨S, rfl⟩ : ∃ S : ℕ, s = (S : ℤ) :=
      ⟨s.toNat, by simp [Int.toNat_of_nonneg (le_of_lt hs)]⟩
    have hS2 : S % 2 = 1 := by exact_mod_cast hs2
    have hS5 : S % 5 = 1 ∨ S % 5 = 4 := by exact_mod_cast hs5
    obtain ⟨q, t, hq, _, hqt⟩ := exists_oddFive_prime S hS2 hS5
    let _ : Fact q.Prime := ⟨hq⟩
    exact oddFive_conditions_of_prime hS2 hS5 hqt
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) :=
      ⟨m.toNat, by simp [Int.toNat_of_nonneg (le_of_lt hm)]⟩
    have hM2 : M % 2 = 1 := by exact_mod_cast hm2
    have hM5 : M % 5 ≠ 0 := by
      intro h
      apply h5
      apply Int.dvd_iff_emod_eq_zero.mpr
      exact_mod_cast h
    obtain ⟨q, t, hq, hq5, hqt⟩ := exists_oddUnit_prime M hM2 hM5
    let _ : Fact q.Prime := ⟨hq⟩
    exact oddUnit_conditions_of_prime hM2 hq5 hqt

/-- The classification at determinant 10 implies `Regular125Sufficiency`.
`ClassicalInputs.Regular125.Classification` proves the classification. -/
theorem regular125Sufficiency_of_classification (hclass : DeterminantTenClassification) :
    Regular125Sufficiency :=
  regular125Sufficiency_of_odd_arithmetic oddParameterArithmetic hclass

end Mordell125

end FibonacciCriterion

