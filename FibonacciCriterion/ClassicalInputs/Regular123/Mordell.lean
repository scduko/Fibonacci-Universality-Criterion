import FibonacciCriterion.ClassicalInputs.ThreeSquares.Obstruction
import FibonacciCriterion.ClassicalInputs.Reduction.Classification
import FibonacciCriterion.ClassicalInputs.Mordell
import FibonacciCriterion.ClassicalInputs.Regular123.SquareRoots
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Sufficiency for `⟨1,2,3⟩`: the Mordell construction

For every `m > 0` with `4 ∤ m` and `m ≢ 10 (mod 16)`, this file constructs a
Mordell datum of determinant 6 for `m` with `a > 0` whose leading coefficient
is odd and `≡ 3 (mod 9)` (`Mordell123DataSynthesis`).
`ClassicalInputs.Regular123.Classification` deduces that `⟨1,2,3⟩` represents
`m` and proves the criterion of Proposition 3.2. The manuscript cites
Jones–Pall for this direction; the construction here is of the Mordell type of
Blackwell–Durham–Thompson–Treece.

## The construction

Let `A`, `a > 0`, and `t` be integers with

* `9m ∣ A² + a - 3m`, so that `C = (A² + a)/m` is an integer `≡ 3 (mod 9)`;
* `a ∣ 6 + mt²`, with quotient `u`.

The Mordell form is `C x² + 2t xy + u y² + 2A xz + m z²`. Its Gram matrix
`[[C, t, A], [t, u, 0], [A, 0, m]]` has determinant `u(Cm - A²) - mt² = 6`. The
form represents `m` at `(0, 0, 1)` and `C` at `(1, 0, 0)`, and it is positive
definite because `a > 0` (`MordellDatum.positive_of_determinant_pos`). Such a
triple, with a parity condition that makes `C` odd, is a
`Mordell123CongruenceRow`; `Mordell123CongruenceRow.toExplicit` builds the
datum.

The parameters are as follows, with `p` a prime from Dirichlet's theorem and
`k ≥ 0`:

| input | `A` | `a` | progression of `p` | `C` |
| --- | --- | --- | --- | --- |
| `m` odd | 2 | `p` | `p ≡ mC₀ - 4 (mod 72m)` | `C₀ + 72k` |
| `m = 2n`, `n ≡ 1 (mod 8)` | 2 | `2p` | `p ≡ 21n - 2 (mod 18n)` | `21 + 18k` |
| `m = 2n`, `n ≡ 3 (mod 4)` | 1 | `p` | `p ≡ 42n - 1 (mod 36n)` | `21 + 18k` |

Here `C₀` is 111 if `m ≡ 1, 3 (mod 8)` and 75 otherwise (`odd123Coefficient`).
The remaining class `n ≡ 5 (mod 8)` is `m ≡ 10 (mod 16)`. In each row
`A² + a = mC` holds by the choice of the progression, so no square root modulo
`m` is extracted and `m` is not factored. The progression also fixes the
residues of `p` that quadratic reciprocity needs for `(-6m/p) = 1`
(`odd123_reciprocity`, `twiceOne123_reciprocity`, `twiceOdd123_reciprocity`),
and a square root of `-6m` modulo `p` gives `t`
(`ClassicalInputs.Regular123.SquareRoots`).

## The classification

The kernel-checked list `detSix` places the eight reduced Gram matrices of
determinant 6 in three classes: `⟨1,1,6⟩`, `⟨1,2,3⟩`, and the even-valued class
`2x² + 2y² + 2z² - 2xy`. The first represents no integer `≡ 3 (mod 9)` and the
last no odd integer, so `⟨1,2,3⟩` represents every integer represented by a
reduced matrix that represents `C` (`represents_q2_of_reduced_separator`).

## Organization

`Mordell123DataSynthesis`, `ExplicitMordell123DataSynthesis`,
`Mordell123ResidueRows`, `Mordell123CongruenceRows`, and
`EvenMordell123CongruenceRows` are statements, each implied by the next
(`dataSynthesis_of_explicit`, `explicitDataSynthesis_of_rows`,
`residueRows_of_congruence`, `congruenceRows_of_even`). The last one is proven
here (`evenMordell123CongruenceRows`, with `oddInputCongruenceRow` for odd
inputs), and `ClassicalInputs.Regular123.Classification` composes the chain.
-/

namespace FibonacciCriterion.Regular123

-- Several proofs install `Fact p.Prime` with `letI`.
set_option linter.style.haveILetI false

open MordellRegularity
open Regular123SquareRoots

/-! ## The reduced determinant-6 matrices -/

/-- The Gram matrix `diag(1, 1, 6)` of the diagonal form `⟨1,1,6⟩`. -/
def q1Gram : TernaryGram := ⟨1, 1, 6, 0, 0, 0⟩
/-- The Gram matrix `diag(1, 2, 3)` of the diagonal form `⟨1,2,3⟩`. -/
def q2Gram : TernaryGram := ⟨1, 2, 3, 0, 0, 0⟩
/-- The Gram matrix `[[2, -1, 0], [-1, 2, 0], [0, 0, 2]]` of the even-valued class
`2x² + 2y² + 2z² - 2xy` of determinant 6. -/
def evenGram : TernaryGram := ⟨2, 2, 2, -1, 0, 0⟩

/-- The classification at determinant 6: the classes `q1Gram = ⟨1,1,6⟩`,
`q2Gram = ⟨1,2,3⟩`, and the even-valued class `evenGram = 2x² + 2y² + 2z² - 2xy`,
with explicit equivalences from the eight reduced Gram matrices. -/
def detSix : TernaryClassification.Classification 6 where
  classes := [q1Gram, q2Gram, evenGram]
  equivalences :=
    [⟨⟨1, 1, 6, 0, 0, 0⟩, q1Gram, ⟨-1, 0, 0, 0, -1, 0, 0, 0, -1⟩⟩,
     ⟨⟨1, 2, 3, 0, 0, 0⟩, q2Gram, ⟨-1, 0, 0, 0, -1, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 2, -1, 0, 0⟩, evenGram, ⟨-1, 0, 0, 0, -1, 0, 0, 0, -1⟩⟩,
     ⟨⟨2, 2, 2, 0, -1, 0⟩, evenGram, ⟨-1, 0, 0, 0, 0, -1, 0, -1, 0⟩⟩,
     ⟨⟨2, 2, 2, 0, 0, -1⟩, evenGram, ⟨0, 0, -1, -1, 0, 0, 0, -1, 0⟩⟩,
     ⟨⟨2, 2, 2, 0, 0, 1⟩, evenGram, ⟨0, 0, -1, -1, 0, 0, 0, 1, 0⟩⟩,
     ⟨⟨2, 2, 2, 0, 1, 0⟩, evenGram, ⟨-1, 0, 0, 0, 0, -1, 0, 1, 0⟩⟩,
     ⟨⟨2, 2, 2, 1, 0, 0⟩, evenGram, ⟨-1, 0, 0, 0, 1, 0, 0, 0, -1⟩⟩]

set_option maxRecDepth 100000 in
/-- Kernel check of `detSix`: the sources of its equivalences are the matrices of
`reducedList 6`, in order; each change of variables is unimodular and carries
its source to its target; and each target is a listed class representative. -/
theorem detSix_check : detSix.Check := by
  decide +kernel

/-- The separator condition at determinant 6: `n ≡ 3 (mod 9)` and `n` is
odd. The classes `⟨1,1,6⟩` and `2x² + 2y² + 2z² - 2xy` represent no such
integer. -/
def Separator123 (n : ℤ) : Prop := n % 9 = 3 ∧ n % 2 = 1

/-! ## The separator -/

/-- Odd input: if `m` and `a` are odd, `A` is even, and `A² + a = mc`, then
`c` is odd. -/
theorem quotient_odd_of_odd_input {m a A c : ℤ}
    (hm : m % 2 = 1) (ha : a % 2 = 1) (hA : A % 2 = 0)
    (heq : A ^ 2 + a = m * c) : c % 2 = 1 := by
  have hc0 : 0 ≤ c % 2 := Int.emod_nonneg _ (by norm_num)
  have hc2 : c % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  have hmod := congrArg (fun t : ℤ => t % 2) heq
  interval_cases hc : c % 2
  all_goals
    norm_num [pow_two, Int.add_emod, Int.mul_emod, hm, ha, hA, hc] at hmod
  all_goals norm_num [hc]

/-- Even input with even `a`: if `m₁` and `a₁` are odd, `A` is even, and
`A² + 2a₁ = 2m₁c`, then `c` is odd. -/
theorem quotient_odd_of_twice_odd_data {m₁ a₁ A c : ℤ}
    (hm₁ : m₁ % 2 = 1) (ha₁ : a₁ % 2 = 1) (hA : A % 2 = 0)
    (heq : A ^ 2 + 2 * a₁ = (2 * m₁) * c) : c % 2 = 1 := by
  obtain ⟨k, hk⟩ := Int.dvd_iff_emod_eq_zero.mpr hA
  have heq' : 2 * k ^ 2 + a₁ = m₁ * c := by
    rw [hk] at heq
    nlinarith [heq]
  have hmod := congrArg (fun t : ℤ => t % 2) heq'
  norm_num [Int.add_emod, Int.mul_emod, hm₁, ha₁] at hmod
  omega

/-- Even input with odd `a`: if `m₁` is odd, `a ≡ 1 (mod 4)`, `A` is odd,
and `A² + a = 2m₁c`, then `c` is odd, since `A² + a ≡ 2 (mod 4)`. -/
theorem quotient_odd_of_twice_odd_input {m₁ a A c : ℤ}
    (hm₁ : m₁ % 2 = 1) (ha : a % 4 = 1) (hA : A % 2 = 1)
    (heq : A ^ 2 + a = (2 * m₁) * c) : c % 2 = 1 := by
  have hAeq : A = 2 * (A / 2) + 1 := by omega
  have haeq : a = 4 * (a / 4) + 1 := by omega
  have heq' : 2 * (A / 2) ^ 2 + 2 * (A / 2) +
      2 * (a / 4) + 1 = m₁ * c := by
    nlinarith [heq, hAeq, haeq]
  have hmod := congrArg (fun t : ℤ => t % 2) heq'
  norm_num [Int.add_emod, Int.mul_emod, hm₁] at hmod
  omega

/-- If `m > 0`, `A² + a = mc`, and `9m ∣ A² + a - 3m`, then `c ≡ 3 (mod 9)`. -/
theorem quotient_mod_nine_of_strong_root {m a A c : ℤ}
    (hm : 0 < m) (heq : A ^ 2 + a = m * c)
    (hdiv : 9 * m ∣ A ^ 2 + a - 3 * m) : c % 9 = 3 := by
  rcases hdiv with ⟨k, hk⟩
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hcancel : c - 3 = 9 * k := by
    apply mul_left_cancel₀ hm0
    calc
      m * (c - 3) = A ^ 2 + a - 3 * m := by rw [heq]; ring
      _ = (9 * m) * k := hk
      _ = m * (9 * k) := by ring
  have hc : c = 9 * k + 3 := by omega
  rw [hc]
  omega

/-- `⟨1,1,6⟩` (`q1Gram`) represents no integer with the separator property (odd
and `≡ 3 (mod 9)`). -/
theorem q1_not_represents_separator {n : ℤ} (hn : Separator123 n) :
    ¬ q1Gram.Represents n := by
  rintro ⟨x, y, z, hxyz⟩
  have hm := congrArg (fun t : ℤ => t % 9) hxyz
  rcases RegularReductions.square_mod_nine x with hx | hx | hx | hx <;>
    rcases RegularReductions.square_mod_nine y with hy | hy | hy | hy <;>
    rcases RegularReductions.square_mod_nine z with hz | hz | hz | hz <;>
    norm_num [q1Gram, TernaryGram.eval, Int.add_emod, Int.mul_emod,
      hx, hy, hz, hn.1] at hm

/-- The even-valued class `2x² + 2y² + 2z² - 2xy` represents no odd integer. -/
theorem even_not_represents_odd {n : ℤ} (hn : n % 2 = 1) :
    ¬ evenGram.Represents n := by
  rintro ⟨x, y, z, hxyz⟩
  have hm := congrArg (fun t : ℤ => t % 2) hxyz
  norm_num [evenGram, TernaryGram.eval, Int.add_emod, Int.mul_emod, hn] at hm

/-- If a reduced Gram matrix of determinant 6 represents an odd integer
`≡ 3 (mod 9)` (`Separator123`), then `⟨1,2,3⟩` represents every integer it
represents. Oddness is needed to exclude the even-valued class
`2x² + 2y² + 2z² - 2xy`. -/
theorem represents_q2_of_reduced_separator (A : TernaryGram)
    (separator input : ℤ) (hA : A ∈ TernaryClassification.reducedList 6)
    (hseparator : A.Represents separator) (hsep : Separator123 separator)
    (hinput : A.Represents input) : q2Gram.Represents input := by
  obtain ⟨T, hT, hAT⟩ := TernaryClassification.Classification.exists_class detSix_check hA
  simp only [detSix, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl
  · exact absurd ((hAT separator).mp hseparator) (q1_not_represents_separator hsep)
  · exact (hAT input).mp hinput
  · exact absurd ((hAT separator).mp hseparator) (even_not_represents_odd hsep.2)

/-! ## Mordell data and congruence rows

A congruence row for `m` (`Mordell123CongruenceRow`) is a triple `A`, `a > 0`,
`t` with `9m ∣ A² + a - 3m` and `a ∣ 6 + mt²`, together with one of three
parity cases (`Mordell123RawParityRow`). The names call the first condition
the strong root condition: it strengthens `m ∣ A² + a` to
`(A² + a)/m ≡ 3 (mod 9)`. The parity case makes `(A² + a)/m` odd.

`Mordell123CongruenceRow.toExplicit` turns a row into a Mordell datum with the
same conditions (`ExplicitMordell123Witness`; `Mordell123ParityRow` is the
parity case restated for the datum), and
`ExplicitMordell123Witness.separator` shows that its leading coefficient
satisfies `Separator123`.

The lemmas `…CongruenceRow_of_strong_root` and `…CongruenceRow_of_legendre`
are stated for an arbitrary solution `A`. The sections "Odd inputs" and "Even
inputs" apply them with `A = 2` or `A = 1`.
-/

/-- The statement of the Mordell construction for `⟨1,2,3⟩`: every `m > 0`
with `4 ∤ m` and `m ≢ 10 (mod 16)` has a Mordell datum of determinant 6 with
`a > 0` and an odd leading coefficient `≡ 3 (mod 9)`. It is proven by
`dataSynthesis_of_congruence_rows` with `congruenceRows_of_even` and
`evenMordell123CongruenceRows`. -/
def Mordell123DataSynthesis : Prop :=
  ∀ m : ℤ, 0 < m → m % 4 ≠ 0 → m % 16 ≠ 10 →
    ∃ d : MordellDatum m 6, 0 < d.a ∧ Separator123 d.cxx

/-- The parity conditions on `m`, `a`, and `A` in the three cases of the
construction: `m` and `a` odd with `A` even; `m = 2m₁` and `a = 2a₁` with
`m₁`, `a₁` odd and `A` even; and `m = 2m₁` with `m₁` odd, `a ≡ 1 (mod 4)`,
and `A` odd. -/
inductive Mordell123RawParityRow (m a A : ℤ) : Prop
  | oddInput
      (hm : m % 2 = 1) (ha : a % 2 = 1) (hA : A % 2 = 0)
  | twiceEvenA (m₁ a₁ : ℤ)
      (hm : m = 2 * m₁) (ha : a = 2 * a₁)
      (hm₁ : m₁ % 2 = 1) (ha₁ : a₁ % 2 = 1) (hA : A % 2 = 0)
  | twiceOddA (m₁ : ℤ)
      (hm : m = 2 * m₁) (hm₁ : m₁ % 2 = 1)
      (ha : a % 4 = 1) (hA : A % 2 = 1)

/-- The congruence data for an input `m`: integers `A`, `a > 0`, and `t` with
`m ∣ A² + a`, `a ∣ 6 + mt²`, `9m ∣ A² + a - 3m`, and one of the parity cases
of `Mordell123RawParityRow`. `Mordell123CongruenceRow.toExplicit` builds the
Mordell datum from them. -/
structure Mordell123CongruenceRow (m : ℤ) where
  /-- The coefficient `A` of the Mordell datum, a square root of `-a` modulo
  `m`. -/
  A : ℤ
  /-- The coefficient `a` of the Mordell datum. In the applications it is `p`
  or `2p` for an auxiliary prime `p`. -/
  a : ℤ
  /-- The integer `t` with `a ∣ 6 + mt²`. The Mordell datum has `h = mt` and
  `cxy = t`. -/
  t : ℤ
  a_pos : 0 < a
  /-- `m ∣ A² + a`, so that `cxx = (A² + a)/m` is an integer. It follows from
  `strong_root` (`xx_dvd_of_123_strong_root`). -/
  xx_dvd : m ∣ A ^ 2 + a
  /-- `a ∣ 6 + mt²`; with quotient `u`, `a(mu) - (mt)² = 6m`. -/
  binary_dvd : a ∣ 6 + m * t ^ 2
  /-- `9m ∣ A² + a - 3m`: the quotient `(A² + a)/m` is `≡ 3 (mod 9)`. -/
  strong_root : 9 * m ∣ A ^ 2 + a - 3 * m
  /-- The parity case, which makes `(A² + a)/m` odd. -/
  parityRow : Mordell123RawParityRow m a A

/-- Odd input: for odd `m` and odd `a > 0` with `a ∣ 6 + mt²`, a solution of
`9m ∣ A² + a - 3m` gives a congruence row. The solution is made even by
`exists_even_123_strong_root`, and `m ∣ A² + a` follows from the congruence
modulo `9m`. -/
theorem oddInputCongruenceRow_of_strong_root {m a t : ℤ}
    (hm : m % 2 = 1) (ha : a % 2 = 1) (hapos : 0 < a)
    (hbinary : a ∣ 6 + m * t ^ 2)
    (hroot : ∃ A : ℤ, 9 * m ∣ A ^ 2 + a - 3 * m) :
    Nonempty (Mordell123CongruenceRow m) := by
  obtain ⟨A, hA⟩ := hroot
  obtain ⟨B, hB, hBeven⟩ := exists_even_123_strong_root hm hA
  exact ⟨{
    A := B
    a := a
    t := t
    a_pos := hapos
    xx_dvd := xx_dvd_of_123_strong_root hB
    binary_dvd := hbinary
    strong_root := hB
    parityRow := Mordell123RawParityRow.oddInput hm ha hBeven
  }⟩

/-- For even `m`, `9m ∣ A² + a - 3m` forces `A ≡ a (mod 2)`. -/
theorem strong_root_parity_of_even_input {m a A : ℤ}
    (hm : m % 2 = 0)
    (hroot : 9 * m ∣ A ^ 2 + a - 3 * m) : A % 2 = a % 2 := by
  obtain ⟨k, hk⟩ := hroot
  have hmod := congrArg (fun t : ℤ => t % 2) hk
  have hAlo : 0 ≤ A % 2 := Int.emod_nonneg _ (by norm_num)
  have hAhi : A % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  have halo : 0 ≤ a % 2 := Int.emod_nonneg _ (by norm_num)
  have hahi : a % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases hA : A % 2 <;> interval_cases ha : a % 2
  all_goals
    norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod,
      hm, hA, ha] at hmod
  all_goals norm_num

/-- Even input `m = 2m₁` with `a = 2a₁`: for odd `m₁` and odd `a₁ > 0` with
`2a₁ ∣ 6 + mt²`, a solution of `9m ∣ A² + 2a₁ - 3m` gives a congruence row.
The solution is even by `strong_root_parity_of_even_input`. -/
theorem twiceEvenACongruenceRow_of_strong_root {m₁ a₁ t : ℤ}
    (hm₁ : m₁ % 2 = 1) (ha₁ : a₁ % 2 = 1) (hapos : 0 < a₁)
    (hbinary : 2 * a₁ ∣ 6 + (2 * m₁) * t ^ 2)
    (hroot : ∃ A : ℤ, 9 * (2 * m₁) ∣ A ^ 2 + 2 * a₁ - 3 * (2 * m₁)) :
    Nonempty (Mordell123CongruenceRow (2 * m₁)) := by
  obtain ⟨A, hA⟩ := hroot
  have hparity : A % 2 = 0 := by
    have h := strong_root_parity_of_even_input
      (by omega : (2 * m₁) % 2 = 0) hA
    omega
  exact ⟨{
    A := A
    a := 2 * a₁
    t := t
    a_pos := by omega
    xx_dvd := xx_dvd_of_123_strong_root hA
    binary_dvd := hbinary
    strong_root := hA
    parityRow := Mordell123RawParityRow.twiceEvenA m₁ a₁
      rfl rfl hm₁ ha₁ hparity
  }⟩

/-- Even input `m = 2m₁` with odd `a`: for odd `m₁` and `a > 0` with
`a ≡ 1 (mod 4)` and `a ∣ 6 + mt²`, a solution of `9m ∣ A² + a - 3m` gives a
congruence row. The solution is odd by `strong_root_parity_of_even_input`. -/
theorem twiceOddACongruenceRow_of_strong_root {m₁ a t : ℤ}
    (hm₁ : m₁ % 2 = 1) (ha : a % 4 = 1) (hapos : 0 < a)
    (hbinary : a ∣ 6 + (2 * m₁) * t ^ 2)
    (hroot : ∃ A : ℤ, 9 * (2 * m₁) ∣ A ^ 2 + a - 3 * (2 * m₁)) :
    Nonempty (Mordell123CongruenceRow (2 * m₁)) := by
  obtain ⟨A, hA⟩ := hroot
  have hparity : A % 2 = 1 := by
    have h := strong_root_parity_of_even_input
      (by omega : (2 * m₁) % 2 = 0) hA
    omega
  exact ⟨{
    A := A
    a := a
    t := t
    a_pos := hapos
    xx_dvd := xx_dvd_of_123_strong_root hA
    binary_dvd := hbinary
    strong_root := hA
    parityRow := Mordell123RawParityRow.twiceOddA m₁ rfl hm₁ ha hparity
  }⟩

/-- Odd input with an odd auxiliary prime `a = p`: if `-6m` is a nonzero
square modulo `p` and `9m ∣ A² + p - 3m` has a solution, then `m` has a
congruence row. The divisibility `p ∣ 6 + mt²` comes from
`exists_123_binary_dvd_of_legendre`. -/
theorem oddInputCongruenceRow_of_legendre
    {m : ℤ} {p : ℕ} [Fact p.Prime]
    (hm : m % 2 = 1) (hpodd : p % 2 = 1) (hppos : 0 < p)
    (hmp : (m : ZMod p) ≠ 0)
    (hdisc : ((-6 * m : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-6 * m) = 1)
    (hroot : ∃ A : ℤ, 9 * m ∣ A ^ 2 + (p : ℤ) - 3 * m) :
    Nonempty (Mordell123CongruenceRow m) := by
  obtain ⟨t, ht⟩ := exists_123_binary_dvd_of_legendre hmp hdisc hleg
  exact oddInputCongruenceRow_of_strong_root hm
    (by exact_mod_cast hpodd) (by exact_mod_cast hppos) ht hroot

/-- Even input `m = 2m₁` with an auxiliary prime `a = p ≡ 1 (mod 4)`: if
`-6m` is a nonzero square modulo `p` and `9m ∣ A² + p - 3m` has a solution,
then `m` has a congruence row. -/
theorem twiceOddACongruenceRow_of_legendre
    {m₁ : ℤ} {p : ℕ} [Fact p.Prime]
    (hm₁ : m₁ % 2 = 1) (hpmod : p % 4 = 1) (hppos : 0 < p)
    (hmp : ((2 * m₁ : ℤ) : ZMod p) ≠ 0)
    (hdisc : ((-6 * (2 * m₁) : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-6 * (2 * m₁)) = 1)
    (hroot : ∃ A : ℤ,
      9 * (2 * m₁) ∣ A ^ 2 + (p : ℤ) - 3 * (2 * m₁)) :
    Nonempty (Mordell123CongruenceRow (2 * m₁)) := by
  obtain ⟨t, ht⟩ := exists_123_binary_dvd_of_legendre hmp hdisc hleg
  exact twiceOddACongruenceRow_of_strong_root hm₁
    (by exact_mod_cast hpmod) (by exact_mod_cast hppos) ht hroot

/-- Even input `m = 2m₁` with `a = 2p` for an odd prime `p`: if `-6m` is a
nonzero square modulo `p` and `9m ∣ A² + 2p - 3m` has a solution, then `m`
has a congruence row. No condition at 2 is needed, since `6 + mt²` is even
and `p` is odd. -/
theorem twiceEvenACongruenceRow_of_legendre
    {m₁ : ℤ} {p : ℕ} [Fact p.Prime]
    (hm₁ : m₁ % 2 = 1) (hpodd : p % 2 = 1) (hppos : 0 < p)
    (hmp : ((2 * m₁ : ℤ) : ZMod p) ≠ 0)
    (hdisc : ((-6 * (2 * m₁) : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-6 * (2 * m₁)) = 1)
    (hroot : ∃ A : ℤ,
      9 * (2 * m₁) ∣ A ^ 2 + 2 * (p : ℤ) - 3 * (2 * m₁)) :
    Nonempty (Mordell123CongruenceRow (2 * m₁)) := by
  obtain ⟨t, ht⟩ := exists_123_twice_binary_dvd_of_legendre hpodd hmp hdisc hleg
  exact twiceEvenACongruenceRow_of_strong_root hm₁
    (by exact_mod_cast hpodd) (by exact_mod_cast hppos) ht hroot

/-- The three parity cases of `Mordell123RawParityRow`, stated for a Mordell
datum. They record only the congruences used to prove that the leading
coefficient is odd. -/
inductive Mordell123ParityRow (m : ℤ) (d : MordellDatum m 6) : Prop
  | oddInput
      (hm : m % 2 = 1) (ha : d.a % 2 = 1) (hA : d.A % 2 = 0)
  | twiceEvenA (m₁ a₁ : ℤ)
      (hm : m = 2 * m₁) (ha : d.a = 2 * a₁)
      (hm₁ : m₁ % 2 = 1) (ha₁ : a₁ % 2 = 1) (hA : d.A % 2 = 0)
  | twiceOddA (m₁ : ℤ)
      (hm : m = 2 * m₁) (hm₁ : m₁ % 2 = 1)
      (ha : d.a % 4 = 1) (hA : d.A % 2 = 1)

/-- A Mordell datum of determinant 6 for `m` with `a > 0`,
`A² + a ≡ 3m (mod 9m)`, and one of the three parity cases. -/
structure ExplicitMordell123Witness (m : ℤ) where
  /-- The Mordell datum of determinant 6 for `m`. -/
  datum : MordellDatum m 6
  a_pos : 0 < datum.a
  strong_root : 9 * m ∣ datum.A ^ 2 + datum.a - 3 * m
  parityRow : Mordell123ParityRow m datum

/-- The leading coefficient of an explicit witness is odd and `≡ 3 (mod 9)`. -/
theorem ExplicitMordell123Witness.separator {m : ℤ}
    (w : ExplicitMordell123Witness m) (hm : 0 < m) :
    Separator123 w.datum.cxx := by
  constructor
  · exact quotient_mod_nine_of_strong_root hm w.datum.xx_eq w.strong_root
  · cases w.parityRow with
    | oddInput hm₂ ha hA =>
        exact quotient_odd_of_odd_input hm₂ ha hA w.datum.xx_eq
    | twiceEvenA m₁ a₁ hmeq haeq hm₁ ha₁ hA =>
        apply quotient_odd_of_twice_odd_data hm₁ ha₁ hA
        simpa [hmeq, haeq] using w.datum.xx_eq
    | twiceOddA m₁ hmeq hm₁ ha hA =>
        apply quotient_odd_of_twice_odd_input hm₁ ha hA
        simpa [hmeq] using w.datum.xx_eq

/-- A congruence row gives a Mordell datum: if `6 + mt² = au`, take `B = 0`,
`h = mt`, `b = mu`, `cxy = t`, and `cyy = u`; then `ab - h² = 6m`. -/
theorem Mordell123CongruenceRow.toExplicit {m : ℤ}
    (w : Mordell123CongruenceRow m) :
    Nonempty (ExplicitMordell123Witness m) := by
  rcases w.xx_dvd with ⟨cxx, hxx⟩
  rcases w.binary_dvd with ⟨u, hu⟩
  have hdet : w.a * (m * u) - (m * w.t) ^ 2 = 6 * m := by
    calc
      w.a * (m * u) - (m * w.t) ^ 2 =
          m * (w.a * u - m * w.t ^ 2) := by ring
      _ = m * ((6 + m * w.t ^ 2) - m * w.t ^ 2) := by rw [← hu]
      _ = 6 * m := by ring
  let d : MordellDatum m 6 :=
    MordellDatum.ofBZero (m := m) (D := 6) (A := w.A) (a := w.a)
      (h := m * w.t) (b := m * u) (cxx := cxx) (cxy := w.t) (cyy := u)
      hxx (by rfl) (by rfl) hdet
  refine ⟨{
    datum := d
    a_pos := by change 0 < w.a; exact w.a_pos
    strong_root := by change 9 * m ∣ w.A ^ 2 + w.a - 3 * m; exact w.strong_root
    parityRow := ?_ }⟩
  cases w.parityRow with
  | oddInput hm ha hA =>
      exact Mordell123ParityRow.oddInput hm
        (by change w.a % 2 = 1; exact ha) (by change w.A % 2 = 0; exact hA)
  | twiceEvenA m₁ a₁ hm ha hm₁ ha₁ hA =>
      exact Mordell123ParityRow.twiceEvenA m₁ a₁ hm
        (by change w.a = 2 * a₁; exact ha) hm₁ ha₁
        (by change w.A % 2 = 0; exact hA)
  | twiceOddA m₁ hm hm₁ ha hA =>
      exact Mordell123ParityRow.twiceOddA m₁ hm hm₁
        (by change w.a % 4 = 1; exact ha) (by change w.A % 2 = 1; exact hA)

/-- The statement that every `m > 0` with `4 ∤ m` and `m ≢ 10 (mod 16)` has an
`ExplicitMordell123Witness`. It follows from `Mordell123ResidueRows`
(`explicitDataSynthesis_of_rows`). -/
def ExplicitMordell123DataSynthesis : Prop :=
  ∀ m : ℤ, 0 < m → m % 4 ≠ 0 → m % 16 ≠ 10 →
    Nonempty (ExplicitMordell123Witness m)

/-- An `ExplicitMordell123Witness` for each of four residue families of the
input: `m ≡ 1 (mod 4)`, `m ≡ 3 (mod 4)`, `m ≡ 2 (mod 16)`, and
`m ≡ 6, 14 (mod 16)`. They cover every `m > 0` with `4 ∤ m` and
`m ≢ 10 (mod 16)` (`explicitDataSynthesis_of_rows`). -/
structure Mordell123ResidueRows : Prop where
  oddOne : ∀ m : ℤ, 0 < m → m % 4 = 1 →
    Nonempty (ExplicitMordell123Witness m)
  oddThree : ∀ m : ℤ, 0 < m → m % 4 = 3 →
    Nonempty (ExplicitMordell123Witness m)
  twiceOne : ∀ m : ℤ, 0 < m → m % 16 = 2 →
    Nonempty (ExplicitMordell123Witness m)
  twiceThreeOrSeven : ∀ m : ℤ, 0 < m →
    (m % 16 = 6 ∨ m % 16 = 14) →
    Nonempty (ExplicitMordell123Witness m)

/-- Congruence rows for the four residue families of
`Mordell123ResidueRows`. The Mordell datum and the classification are
supplied separately (`residueRows_of_congruence`,
`represents_q2_of_reduced_separator`). -/
structure Mordell123CongruenceRows : Prop where
  oddOne : ∀ m : ℤ, 0 < m → m % 4 = 1 →
    Nonempty (Mordell123CongruenceRow m)
  oddThree : ∀ m : ℤ, 0 < m → m % 4 = 3 →
    Nonempty (Mordell123CongruenceRow m)
  twiceOne : ∀ m : ℤ, 0 < m → m % 16 = 2 →
    Nonempty (Mordell123CongruenceRow m)
  twiceThreeOrSeven : ∀ m : ℤ, 0 < m →
    (m % 16 = 6 ∨ m % 16 = 14) →
    Nonempty (Mordell123CongruenceRow m)

/-- Congruence rows for the four residue families give explicit witnesses for
them, by `Mordell123CongruenceRow.toExplicit`. -/
theorem residueRows_of_congruence (C : Mordell123CongruenceRows) :
    Mordell123ResidueRows where
  oddOne m hm hr := by
    rcases C.oddOne m hm hr with ⟨w⟩
    exact w.toExplicit
  oddThree m hm hr := by
    rcases C.oddThree m hm hr with ⟨w⟩
    exact w.toExplicit
  twiceOne m hm hr := by
    rcases C.twiceOne m hm hr with ⟨w⟩
    exact w.toExplicit
  twiceThreeOrSeven m hm hr := by
    rcases C.twiceThreeOrSeven m hm hr with ⟨w⟩
    exact w.toExplicit

/-- The four residue families cover every `m > 0` with `4 ∤ m` and
`m ≢ 10 (mod 16)`. -/
theorem explicitDataSynthesis_of_rows (R : Mordell123ResidueRows) :
    ExplicitMordell123DataSynthesis := by
  intro m hm hm4 hm16
  by_cases h1 : m % 4 = 1
  · exact R.oddOne m hm h1
  by_cases h3 : m % 4 = 3
  · exact R.oddThree m hm h3
  have h2 : m % 4 = 2 := by
    have hlo : 0 ≤ m % 4 := Int.emod_nonneg _ (by norm_num)
    have hhi : m % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  have hr : m % 16 = 2 ∨ m % 16 = 6 ∨ m % 16 = 10 ∨ m % 16 = 14 := by
    have hlo : 0 ≤ m % 16 := Int.emod_nonneg _ (by norm_num)
    have hhi : m % 16 < 16 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  rcases hr with hr | hr | hr | hr
  · exact R.twiceOne m hm hr
  · exact R.twiceThreeOrSeven m hm (Or.inl hr)
  · exact False.elim (hm16 hr)
  · exact R.twiceThreeOrSeven m hm (Or.inr hr)

/-- An explicit witness for every admissible `m` gives `Mordell123DataSynthesis`:
its datum has `a > 0`, and its leading coefficient satisfies `Separator123`
(`ExplicitMordell123Witness.separator`). -/
theorem dataSynthesis_of_explicit (S : ExplicitMordell123DataSynthesis) :
    Mordell123DataSynthesis := by
  intro m hm hm4 hm16
  let w := Classical.choice (S m hm hm4 hm16)
  exact ⟨w.datum, w.a_pos, w.separator hm⟩

/-- Congruence rows for the four residue families give
`Mordell123DataSynthesis`. -/
theorem dataSynthesis_of_congruence_rows (C : Mordell123CongruenceRows) :
    Mordell123DataSynthesis :=
  dataSynthesis_of_explicit
    (explicitDataSynthesis_of_rows (residueRows_of_congruence C))

/-! ## Odd inputs

Take `A = 2` and `a = p`, a prime with `p ≡ mC₀ - 4 (mod 72m)`, where
`C₀ = odd123Coefficient m` is 111 or 75 (`odd123Residue m = mC₀ - 4`). Then
`4 + p = mC` with `C = C₀ + 72k`, odd and `≡ 3 (mod 9)`, so `A = 2` satisfies
`9m ∣ A² + p - 3m`. The input is not factored and may be divisible by any
power of 3.

The two values of `C₀` make `p ≡ 11 (mod 24)` when `m ≡ 1 (mod 4)` and
`p ≡ 17 (mod 24)` when `m ≡ 3 (mod 4)` (`odd123_residue_mod`). Then
`(-3/p) = -1`; and since `p ≡ -4 (mod m)`, `(m/p) = (-1/m)` and
`(2/p)(-1/m) = -1`. Hence `(-6m/p) = 1` (`odd123_reciprocity`).
-/

/-- The base value of the leading coefficient `C` for odd `m`: 111 if
`m ≡ 1, 3 (mod 8)` and 75 otherwise. Both values are odd and
`≡ 3 (mod 9)`; the Mordell form has `C = odd123Coefficient m + 72k`. -/
def odd123Coefficient (m : ℕ) : ℕ :=
  if m % 8 = 1 ∨ m % 8 = 3 then 111 else 75

/-- The residue `m · odd123Coefficient m - 4` of the auxiliary prime `p`
modulo `72m` for odd `m`. It gives `4 + p = mC` with
`C ≡ odd123Coefficient m (mod 72)`. -/
def odd123Residue (m : ℕ) : ℕ := m * odd123Coefficient m - 4

/-- For `m > 0`, `4 + odd123Residue m = m · odd123Coefficient m`; the
natural-number subtraction does not truncate. -/
theorem odd123_residue_identity {m : ℕ} (hm : 0 < m) :
    4 + odd123Residue m = m * odd123Coefficient m := by
  unfold odd123Residue odd123Coefficient
  split_ifs <;> omega

/-- For odd `m > 0`, `odd123Residue m` is 11 modulo 24 if `m ≡ 1 (mod 4)` and
17 modulo 24 if `m ≡ 3 (mod 4)`, the classes that `odd123_reciprocity`
requires. -/
theorem odd123_residue_mod {m : ℕ} (hm : 0 < m) (ho : m % 2 = 1) :
    (m % 4 = 1 ∧ odd123Residue m % 24 = 11) ∨
    (m % 4 = 3 ∧ odd123Residue m % 24 = 17) := by
  have hhi := Nat.mod_lt m (by norm_num : 0 < 8)
  interval_cases h : m % 8 <;>
    simp [odd123Residue, odd123Coefficient, h] <;> omega

/-- For odd `m > 0`, `odd123Residue m` is prime to `72m`, so Dirichlet's
theorem applies to its class. -/
theorem odd123_residue_coprime {m : ℕ} (hm : 0 < m) (ho : m % 2 = 1) :
    (odd123Residue m).Coprime (72 * m) := by
  let r := odd123Residue m
  have hm2 : m.Coprime 2 := by
    rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    simp [Nat.dvd_iff_mod_eq_zero, ho]
  have hm4 : m.Coprime 4 := by
    simpa using hm2.pow_right 2
  have hrm : r.Coprime m := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hsum : r.gcd m ∣ 4 + r := by
      rw [odd123_residue_identity hm]
      exact (Nat.gcd_dvd_right r m).mul_right _
    have hfour : r.gcd m ∣ 4 :=
      (Nat.dvd_add_iff_right (Nat.gcd_dvd_left r m)).mpr
        (by simpa [Nat.add_comm] using hsum)
    apply Nat.dvd_one.mp
    rw [← hm4.gcd_eq_one]
    exact Nat.dvd_gcd (Nat.gcd_dvd_right r m) hfour
  have hr72 : r.Coprime 72 := by
    have hr2 : r.Coprime 2 := by
      rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
      rcases odd123_residue_mod hm ho with ⟨_, h⟩ | ⟨_, h⟩ <;>
        simp only [Nat.dvd_iff_mod_eq_zero] <;> change r % 2 ≠ 0 <;> dsimp [r] <;> omega
    have hr3 : r.Coprime 3 := by
      rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
      rcases odd123_residue_mod hm ho with ⟨_, h⟩ | ⟨_, h⟩ <;>
        simp only [Nat.dvd_iff_mod_eq_zero] <;> change r % 3 ≠ 0 <;> dsimp [r] <;> omega
    simpa using (hr2.pow_right 3).mul_right (hr3.pow_right 2)
  exact hr72.mul_right hrm

/-- For odd `p ≡ 2 (mod 3)`, the Jacobi symbol `(-3/p)` is -1; `p` need
not be prime. -/
theorem odd123_jacobi_neg_three {p : ℕ} (ho : Odd p) (h3 : p % 3 = 2) :
    jacobiSym (-3) p = -1 := by
  rw [jacobi_neg_three_swap ho, jacobiSym.mod_left, ← Int.natCast_mod]
  norm_num [h3]

/-- Reciprocity for odd inputs: if `m` is odd, `p` is a prime with `4 + p = mC`,
and either `m ≡ 1 (mod 4)` and `p ≡ 11 (mod 24)` or `m ≡ 3 (mod 4)` and
`p ≡ 17 (mod 24)`, then `(-6m/p) = 1`. -/
theorem odd123_reciprocity {m p C : ℕ} (ho : m % 2 = 1)
    (hp : p.Prime) (hid : 4 + p = m * C)
    (hrow : (m % 4 = 1 ∧ p % 24 = 11) ∨
      (m % 4 = 3 ∧ p % 24 = 17)) :
    @legendreSym p ⟨hp⟩ (-6 * (m : ℤ)) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hmO : Odd m := Nat.odd_iff.mpr ho
  have hpO : Odd p := Nat.odd_iff.mpr (by rcases hrow with h | h <;> omega)
  have hp3 : p % 3 = 2 := by rcases hrow with h | h <;> omega
  have hpm : jacobiSym (p : ℤ) m = ZMod.χ₄ m := by
    have hcong : (p : ℤ) ≡ -4 [ZMOD (m : ℤ)] := by
      apply Int.modEq_iff_add_fac.mpr
      refine ⟨-(C : ℤ), ?_⟩
      have hz : (4 : ℤ) + (p : ℤ) = (m : ℤ) * (C : ℤ) := by exact_mod_cast hid
      linear_combination -hz
    rw [jacobiSym.mod_left' hcong,
      show (-4 : ℤ) = -(4 : ℤ) by norm_num,
      jacobiSym.neg _ hmO, jacobiSym.at_four hmO, mul_one]
  have hswap : jacobiSym (m : ℤ) p = ZMod.χ₄ m := by
    rcases hrow with ⟨hm4, hp24⟩ | ⟨hm4, hp24⟩
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four hm4 hpO, hpm]
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four' hmO (by omega), hpm]
  have hsign : ZMod.χ₈ p * ZMod.χ₄ m = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four]
    rcases hrow with h | h <;> split_ifs <;> omega
  rw [jacobiSym.legendreSym.to_jacobiSym,
    show (-6 * (m : ℤ)) = (-3) * (2 * (m : ℤ)) by ring,
    jacobiSym.mul_left, odd123_jacobi_neg_three hpO hp3,
    jacobiSym.mul_left, jacobiSym.at_two hpO, hswap, hsign]
  norm_num

/-- Every odd `m > 0` has a congruence row, with `A = 2` and an auxiliary
prime `p ≡ odd123Residue m (mod 72m)` from Dirichlet's theorem. -/
theorem oddInputCongruenceRow {m : ℕ} (hm : 0 < m) (ho : m % 2 = 1) :
    Nonempty (Mordell123CongruenceRow (m : ℤ)) := by
  obtain ⟨p, hlarge, hp, hmod⟩ := exists_auxiliary_prime
    (6 * m + odd123Residue m) (72 * m) (odd123Residue m)
    (by positivity) (odd123_residue_coprime hm ho)
  have hle : odd123Residue m ≤ p := by omega
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  have hpk : p = odd123Residue m + (72 * m) * k := by omega
  have hid : 4 + p = m * (odd123Coefficient m + 72 * k) := by
    rw [hpk, ← Nat.add_assoc, odd123_residue_identity hm]
    ring
  have hp24 : p % 24 = odd123Residue m % 24 :=
    hmod.of_dvd (by exact ⟨3 * m, by ring⟩)
  have hrow : (m % 4 = 1 ∧ p % 24 = 11) ∨
      (m % 4 = 3 ∧ p % 24 = 17) := by
    simpa only [hp24] using odd123_residue_mod hm ho
  letI : Fact p.Prime := ⟨hp⟩
  have hmp : ((m : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ m := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) p).mp hz
    exact (Nat.not_dvd_of_pos_of_lt hm (by omega)) hd
  have hdisc : ((-6 * (m : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hd : (p : ℤ) ∣ -6 * (m : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hd' : p ∣ 6 * m := by
      have : (p : ℤ) ∣ (6 * m : ℕ) := by simpa using (dvd_neg.mp hd)
      exact_mod_cast this
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) (by omega)) hd'
  apply oddInputCongruenceRow_of_legendre (by exact_mod_cast ho)
    (by rcases hrow with h | h <;> omega) hp.pos hmp hdisc
    (odd123_reciprocity ho hp hid hrow)
  refine ⟨2, ?_⟩
  have hz : (4 : ℤ) + (p : ℤ) =
      (m : ℤ) * ((odd123Coefficient m : ℤ) + 72 * (k : ℤ)) := by
    exact_mod_cast hid
  have hC : ∃ t : ℤ, (odd123Coefficient m : ℤ) = 3 + 9 * t := by
    unfold odd123Coefficient
    split_ifs
    · exact ⟨12, by norm_num⟩
    · exact ⟨8, by norm_num⟩
  obtain ⟨t, ht⟩ := hC
  refine ⟨t + 8 * (k : ℤ), ?_⟩
  rw [ht] at hz
  nlinarith [hz]

/-- Congruence rows for the two even residue families, `m ≡ 2 (mod 16)` and
`m ≡ 6, 14 (mod 16)`. With `oddInputCongruenceRow` they give
`Mordell123CongruenceRows` (`congruenceRows_of_even`). -/
structure EvenMordell123CongruenceRows : Prop where
  twiceOne : ∀ m : ℤ, 0 < m → m % 16 = 2 →
    Nonempty (Mordell123CongruenceRow m)
  twiceThreeOrSeven : ∀ m : ℤ, 0 < m →
    (m % 16 = 6 ∨ m % 16 = 14) →
    Nonempty (Mordell123CongruenceRow m)

/-- `oddInputCongruenceRow` for an integer `m > 0`. -/
theorem oddInputCongruenceRow_int {m : ℤ} (hm : 0 < m) (ho : m % 2 = 1) :
    Nonempty (Mordell123CongruenceRow m) := by
  have hc : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm.le
  have hn : 0 < m.toNat := by omega
  have hodd : m.toNat % 2 = 1 := by omega
  simpa only [hc] using oddInputCongruenceRow hn hodd

/-- The even rows, with `oddInputCongruenceRow` for odd inputs, give congruence
rows for all four residue families. -/
theorem congruenceRows_of_even (E : EvenMordell123CongruenceRows) :
    Mordell123CongruenceRows where
  oddOne m hm hmod := oddInputCongruenceRow_int hm (by omega)
  oddThree m hm hmod := oddInputCongruenceRow_int hm (by omega)
  twiceOne := E.twiceOne
  twiceThreeOrSeven := E.twiceThreeOrSeven

/-! ## Even inputs

Write `m = 2n` with `n` odd; `n ≡ 5 (mod 8)` is the excluded class
`m ≡ 10 (mod 16)`. In both cases below the leading coefficient is
`C = 21 + 18k`, and `(-6m/p) = (-3/p)(n/p)` because `-6m = (-3) · 4n`.

* `n ≡ 1 (mod 8)`: `A = 2`, `a = 2p`, `p ≡ 21n - 2 (mod 18n)`. Then
  `2 + p = nC`, `p` is odd, and `p ≡ 1 (mod 3)`, so `(-3/p) = 1` and
  `(n/p) = (-2/n) = 1` (`twiceOne123_reciprocity`).
* `n ≡ 3 (mod 4)`: `A = 1`, `a = p`, `p ≡ 42n - 1 (mod 36n)`. Then
  `1 + p = mC`, `p ≡ 1 (mod 4)`, and `p ≡ 2 (mod 3)`, so `(-3/p) = -1` and
  `(n/p) = (-1/n) = -1` (`twiceOdd123_reciprocity`).
-/

/-- Reciprocity for `m = 2n` with `n ≡ 1 (mod 8)`: if `p` is an odd prime with
`p ≡ 1 (mod 3)` and `2 + p = nC`, then `(-6m/p) = 1`. -/
theorem twiceOne123_reciprocity {n p C : ℕ} (hn : n % 8 = 1)
    (hp : p.Prime) (ho : p % 2 = 1) (hp3 : p % 3 = 1)
    (hid : 2 + p = n * C) :
    @legendreSym p ⟨hp⟩ (-6 * (2 * (n : ℤ))) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnO : Odd n := Nat.odd_iff.mpr (by omega)
  have hpO : Odd p := Nat.odd_iff.mpr ho
  have hcong : (p : ℤ) ≡ -2 [ZMOD (n : ℤ)] := by
    apply Int.modEq_iff_add_fac.mpr
    refine ⟨-(C : ℤ), ?_⟩
    have hz : (2 : ℤ) + (p : ℤ) = (n : ℤ) * (C : ℤ) := by exact_mod_cast hid
    linear_combination -hz
  have hnp : jacobiSym (n : ℤ) p = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four (by omega : n % 4 = 1) hpO,
      jacobiSym.mod_left' hcong, jacobiSym.neg _ hnO, jacobiSym.at_two hnO,
      ZMod.χ₄_nat_one_mod_four (by omega), ZMod.χ₈_nat_eq_if_mod_eight]
    norm_num [hn, show n % 2 = 1 by omega]
  have hthree : jacobiSym (-3) p = 1 := by
    rw [jacobi_neg_three_swap hpO, jacobiSym.mod_left, ← Int.natCast_mod]
    norm_num [hp3]
  rw [jacobiSym.legendreSym.to_jacobiSym,
    show -6 * (2 * (n : ℤ)) = (-3) * (4 * (n : ℤ)) by ring,
    jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_four hpO, hthree, hnp]
  norm_num

/-- Reciprocity for `m = 2n` with `n ≡ 3 (mod 4)`: if `p` is a prime with
`p ≡ 1 (mod 4)`, `p ≡ 2 (mod 3)`, and `1 + p = mC`, then `(-6m/p) = 1`. -/
theorem twiceOdd123_reciprocity {n p C : ℕ} (hn : n % 4 = 3)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp3 : p % 3 = 2)
    (hid : 1 + p = 2 * n * C) :
    @legendreSym p ⟨hp⟩ (-6 * (2 * (n : ℤ))) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnO : Odd n := Nat.odd_iff.mpr (by omega)
  have hpO : Odd p := Nat.odd_iff.mpr (by omega)
  have hcong : (p : ℤ) ≡ -1 [ZMOD (n : ℤ)] := by
    apply Int.modEq_iff_add_fac.mpr
    refine ⟨-2 * (C : ℤ), ?_⟩
    have hz : (1 : ℤ) + (p : ℤ) = 2 * (n : ℤ) * (C : ℤ) := by exact_mod_cast hid
    linear_combination -hz
  have hnp : jacobiSym (n : ℤ) p = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hnO hp4,
      jacobiSym.mod_left' hcong, jacobiSym.neg _ hnO,
      jacobiSym.one_left, ZMod.χ₄_nat_three_mod_four hn]
    norm_num
  rw [jacobiSym.legendreSym.to_jacobiSym,
    show -6 * (2 * (n : ℤ)) = (-3) * (4 * (n : ℤ)) by ring,
    jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_four hpO,
    odd123_jacobi_neg_three hpO hp3, hnp]
  norm_num

/-- For odd `n > 0`, `21n - 2` is prime to `18n` and `42n - 1` is prime to
`36n`, so Dirichlet's theorem applies to the two progressions of the even
inputs. -/
theorem even123_residue_coprime {n : ℕ} (hn : 0 < n) (ho : n % 2 = 1) :
    (21 * n - 2).Coprime (18 * n) ∧
      (42 * n - 1).Coprime (36 * n) := by
  have hn2 : n.Coprime 2 := by
    rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    simp [Nat.dvd_iff_mod_eq_zero, ho]
  have hfirst : (21 * n - 2).Coprime n := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hs : (21 * n - 2).gcd n ∣ 2 + (21 * n - 2) := by
      rw [show 2 + (21 * n - 2) = 21 * n by omega]
      exact (Nat.gcd_dvd_right _ _).mul_left _
    have htwo : (21 * n - 2).gcd n ∣ 2 :=
      (Nat.dvd_add_iff_right (Nat.gcd_dvd_left _ _)).mpr
        (by simpa [Nat.add_comm] using hs)
    apply Nat.dvd_one.mp
    rw [← hn2.gcd_eq_one]
    exact Nat.dvd_gcd (Nat.gcd_dvd_right _ _) htwo
  have hsecond : (42 * n - 1).Coprime n := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hs : (42 * n - 1).gcd n ∣ 1 + (42 * n - 1) := by
      rw [show 1 + (42 * n - 1) = 42 * n by omega]
      exact (Nat.gcd_dvd_right _ _).mul_left _
    exact Nat.dvd_one.mp
      ((Nat.dvd_add_iff_right (Nat.gcd_dvd_left _ _)).mpr
        (by simpa [Nat.add_comm] using hs))
  have hf2 : (21 * n - 2).Coprime 2 := by
    rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  have hf3 : (21 * n - 2).Coprime 3 := by
    rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  have hs2 : (42 * n - 1).Coprime 2 := by
    rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  have hs3 : (42 * n - 1).Coprime 3 := by
    rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  exact ⟨(by simpa using (hf2.mul_right (hf3.pow_right 2)).mul_right hfirst),
    (by simpa using ((hs2.pow_right 2).mul_right (hs3.pow_right 2)).mul_right hsecond)⟩

/-- If `12n < p`, then `2n` and `-6(2n)` are nonzero modulo `p`. -/
theorem even123_nonzero {n p : ℕ} (hn : 0 < n) (hlarge : 12 * n < p) :
    ((2 * (n : ℤ) : ℤ) : ZMod p) ≠ 0 ∧
    ((-6 * (2 * (n : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
  constructor
  · intro hz
    have hd : p ∣ 2 * n := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) (by omega)) hd
  · intro hz
    have hd : (p : ℤ) ∣ -6 * (2 * (n : ℤ)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hd' : p ∣ 12 * n := by
      have hneg : (p : ℤ) ∣ -(6 * (2 * (n : ℤ))) := by
        simpa only [neg_mul] using hd
      have hpos : (p : ℤ) ∣ 6 * (2 * (n : ℤ)) := dvd_neg.mp hneg
      have hmul : 6 * (2 * n) = 12 * n := by ring
      rw [← hmul]
      exact_mod_cast hpos
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) hlarge) hd'

/-- Every `m = 2n` with `n ≡ 1 (mod 8)` has a congruence row; the auxiliary prime
is `p ≡ 21n - 2 (mod 18n)`, from Dirichlet's theorem. -/
theorem twiceOne123CongruenceRow {n : ℕ} (hn : 0 < n) (hmod : n % 8 = 1) :
    Nonempty (Mordell123CongruenceRow (2 * (n : ℤ))) := by
  obtain ⟨p, hlarge, hp, hres⟩ := exists_auxiliary_prime
    (12 * n + (21 * n - 2)) (18 * n) (21 * n - 2)
    (by positivity) (even123_residue_coprime hn (by omega)).1
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (show 21 * n - 2 ≤ p by omega)).mp hres.symm
  have hpk : p = (21 * n - 2) + 18 * n * k := by omega
  have hid : 2 + p = n * (21 + 18 * k) := by
    rw [hpk]
    have : 2 + (21 * n - 2) = 21 * n := by omega
    nlinarith
  have hp2 : p % 2 = 1 := by
    have h := hres.of_dvd (show 2 ∣ 18 * n from ⟨9 * n, by ring⟩)
    change p % 2 = (21 * n - 2) % 2 at h
    omega
  have hp3 : p % 3 = 1 := by
    have h := hres.of_dvd (show 3 ∣ 18 * n from ⟨6 * n, by ring⟩)
    change p % 3 = (21 * n - 2) % 3 at h
    omega
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hmp, hdisc⟩ := even123_nonzero hn (show 12 * n < p by omega)
  apply twiceEvenACongruenceRow_of_legendre (by omega) hp2 hp.pos hmp hdisc
    (twiceOne123_reciprocity hmod hp hp2 hp3 hid)
  refine ⟨2, 2 + 2 * (k : ℤ), ?_⟩
  have hz : (2 : ℤ) + (p : ℤ) = (n : ℤ) * (21 + 18 * (k : ℤ)) := by
    exact_mod_cast hid
  nlinarith [hz]

/-- Every `m = 2n` with `n ≡ 3 (mod 4)` has a congruence row; the auxiliary prime
is `p ≡ 42n - 1 (mod 36n)`, from Dirichlet's theorem. -/
theorem twiceOdd123CongruenceRow {n : ℕ} (hn : 0 < n) (hmod : n % 4 = 3) :
    Nonempty (Mordell123CongruenceRow (2 * (n : ℤ))) := by
  obtain ⟨p, hlarge, hp, hres⟩ := exists_auxiliary_prime
    (12 * n + (42 * n - 1)) (36 * n) (42 * n - 1)
    (by positivity) (even123_residue_coprime hn (by omega)).2
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (show 42 * n - 1 ≤ p by omega)).mp hres.symm
  have hpk : p = (42 * n - 1) + 36 * n * k := by omega
  have hid : 1 + p = 2 * n * (21 + 18 * k) := by
    rw [hpk]
    have : 1 + (42 * n - 1) = 42 * n := by omega
    nlinarith
  have hp4 : p % 4 = 1 := by
    have h := hres.of_dvd (show 4 ∣ 36 * n from ⟨9 * n, by ring⟩)
    change p % 4 = (42 * n - 1) % 4 at h
    omega
  have hp3 : p % 3 = 2 := by
    have h := hres.of_dvd (show 3 ∣ 36 * n from ⟨12 * n, by ring⟩)
    change p % 3 = (42 * n - 1) % 3 at h
    omega
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hmp, hdisc⟩ := even123_nonzero hn (show 12 * n < p by omega)
  apply twiceOddACongruenceRow_of_legendre (by omega) hp4 hp.pos hmp hdisc
    (twiceOdd123_reciprocity hmod hp hp4 hp3 hid)
  refine ⟨1, 2 + 2 * (k : ℤ), ?_⟩
  have hz : (1 : ℤ) + (p : ℤ) = 2 * (n : ℤ) * (21 + 18 * (k : ℤ)) := by
    exact_mod_cast hid
  nlinarith [hz]

/-- The two even residue families have congruence rows: `twiceOne123CongruenceRow`
and `twiceOdd123CongruenceRow`. -/
theorem evenMordell123CongruenceRows : EvenMordell123CongruenceRows where
  twiceOne m hm hr := by
    let n := (m / 2).toNat
    have hn : 0 < n := by dsimp [n]; omega
    have hn8 : n % 8 = 1 := by dsimp [n]; omega
    have heq : 2 * (n : ℤ) = m := by dsimp [n]; omega
    simpa only [heq] using twiceOne123CongruenceRow hn hn8
  twiceThreeOrSeven m hm hr := by
    let n := (m / 2).toNat
    have hn : 0 < n := by dsimp [n]; rcases hr with hr | hr <;> omega
    have hn4 : n % 4 = 3 := by dsimp [n]; rcases hr with hr | hr <;> omega
    have heq : 2 * (n : ℤ) = m := by dsimp [n]; rcases hr with hr | hr <;> omega
    simpa only [heq] using twiceOdd123CongruenceRow hn hn4

end FibonacciCriterion.Regular123
