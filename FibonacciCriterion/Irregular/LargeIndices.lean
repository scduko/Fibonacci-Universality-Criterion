import FibonacciCriterion.Irregular.SevenUniversal
import FibonacciCriterion.Irregular.RestrictedCover

/-!
# Fibonacci numbers from index 48 for `f ⊥ ⟨q⟩` (Proposition 6.1)

`representsFPlus_fib_of_forty_eight_le` proves Proposition 6.1 from index 48 onward: for
every `q ∈ Q₇`, `f ⊥ ⟨q⟩` represents `Fₙ` for `n ≥ 48`. The case `q = 7` is
handled by Proposition 6.2. Every other value of `q` uses the small
subtraction of Lemma 6.4 outside the residue pairs (7). For those pairs,
Lemmas 6.5 and 6.6 apply from index 61. Between 48 and 60 only `F₅₇` and
`F₅₈` are 7 or 10 modulo 12; for them the small-prime table
(`smallPrimeTable`) has one row per index and value of `q`, twenty-seven
rows in all, which the manuscript groups into five rows by prime.
-/

namespace FibonacciCriterion.Irregular

open RestrictedCover

/-- A row `(n, q, p, k)` of the small-prime table in the proof of
Proposition 6.1: an index, a value of `q`, a prime with a square transfer, and
a root. -/
structure SmallPrimeRow where
  /-- The index `n` of the Fibonacci number `Fₙ`. -/
  index : ℕ
  /-- The value of `q` in `f ⊥ ⟨q⟩`. -/
  coefficient : ℕ
  /-- The prime `p`. -/
  prime : ℕ
  /-- The root `k` of the congruence `Fₙ ≡ q k² (mod p)`. -/
  root : ℕ

/-- The checks for one row: `p ≠ 2` is in `transferPrimes`, `p ∤ q`, `p ∤ k`,
`Fₙ ≡ q k² (mod p)`, and `q ⌊7p²/2⌋² < Fₙ`, the subtraction bound of
Lemma 6.5. -/
def SmallPrimeRow.check (e : SmallPrimeRow) : Bool :=
  decide ((e.prime : ℤ) ∈ transferPrimes ∧ e.prime ≠ 2 ∧
    e.coefficient % e.prime ≠ 0 ∧ e.root % e.prime ≠ 0 ∧
    Nat.fastFib e.index % e.prime = e.coefficient * e.root ^ 2 % e.prime ∧
    e.coefficient * (7 * e.prime ^ 2 / 2) ^ 2 < Nat.fastFib e.index)

/-- The small-prime table for the indices 57 and 58. -/
def smallPrimeTable : List SmallPrimeRow :=
  [⟨57, 3, 5, 2⟩, ⟨57, 12, 5, 1⟩, ⟨57, 168, 5, 2⟩, ⟨57, 483, 5, 2⟩, ⟨57, 672, 5, 1⟩,
   ⟨57, 903, 5, 2⟩, ⟨57, 84, 11, 4⟩, ⟨57, 315, 11, 4⟩, ⟨57, 336, 11, 2⟩, ⟨57, 756, 11, 5⟩,
   ⟨57, 231, 13, 2⟩, ⟨57, 924, 13, 1⟩, ⟨57, 15, 17, 1⟩, ⟨57, 819, 19, 1⟩,
   ⟨58, 9, 5, 1⟩, ⟨58, 21, 5, 2⟩, ⟨58, 84, 5, 1⟩, ⟨58, 189, 5, 1⟩, ⟨58, 336, 5, 2⟩,
   ⟨58, 609, 5, 1⟩, ⟨58, 756, 5, 2⟩, ⟨58, 924, 5, 1⟩, ⟨58, 525, 11, 2⟩, ⟨58, 777, 11, 5⟩,
   ⟨58, 12, 13, 5⟩, ⟨58, 168, 13, 5⟩, ⟨58, 672, 13, 4⟩]

/-- Every row of the small-prime table passes `SmallPrimeRow.check`. -/
theorem smallPrimeTable_checked : smallPrimeTable.all SmallPrimeRow.check = true := by
  decide +kernel

/-- Every value of `q` other than 7 that meets a pair in (7) at index 57 or 58
has a row in the table at that index. -/
theorem smallPrimeTable_complete :
    irregularCoefficients.all (fun q => decide (q = 7 ∨
      ((¬ BadResidue q (Nat.fastFib 57 % 12) ∨
          ∃ e ∈ smallPrimeTable, e.index = 57 ∧ e.coefficient = q) ∧
        (¬ BadResidue q (Nat.fastFib 58 % 12) ∨
          ∃ e ∈ smallPrimeTable, e.index = 58 ∧ e.coefficient = q)))) = true := by
  decide +kernel

/-- Between indices 48 and 60, only `F₅₇` and `F₅₈` are 7 or 10 modulo 12. -/
theorem middle_window_residues :
    (List.range 13).all (fun j => decide (j + 48 = 57 ∨ j + 48 = 58 ∨
      (Nat.fastFib (j + 48) % 12 ≠ 7 ∧ Nat.fastFib (j + 48) % 12 ≠ 10))) = true := by
  decide +kernel

/-- Every prime `p` of `P₇` is in `transferPrimes`, is not 2, and satisfies
`⌊7p²/2⌋ ≤ 41583`. -/
theorem coverPrimes_checked :
    coverPrimes.all (fun p => decide ((p : ℤ) ∈ transferPrimes ∧ p ≠ 2 ∧
      7 * p ^ 2 / 2 ≤ 41583)) = true := by
  decide +kernel

/-- Every value of `q` other than 7 that is 0, 3, or 9 modulo 12, and so can
meet a pair in (7), lies in `restrictedCoefficients`. -/
theorem restrictedCoefficients_complete :
    irregularCoefficients.all (fun q => decide (q = 7 ∨
      ¬ (q % 12 = 0 ∨ q % 12 = 3 ∨ q % 12 = 9) ∨ q ∈ restrictedCoefficients)) = true := by
  decide +kernel

/-- The two size bounds in the proof of Proposition 6.1: `441 · 1022 < F₄₈`, so
Lemma 6.4 applies from index 48, and `B* = 1022 · 41583² < F₆₁`, the bound (9),
so Lemma 6.5 applies from index 61. -/
theorem fib_growth_values :
    441 * 1022 < Nat.fastFib 48 ∧ 1022 * 41583 ^ 2 < Nat.fastFib 61 := by
  decide +kernel

/-- The two forms of the pairs (7) agree: `BadPair` on integers and `BadResidue`
on a value of `q` and a residue modulo 12. -/
theorem badPair_iff (q N : ℕ) :
    BadPair (q : ℤ) (N : ℤ) ↔ BadResidue q (N % 12) := by
  unfold BadPair BadResidue
  omega

/-- Lemma 6.5 for `q ∈ Q₇ \ {7}` and `N = Fₙ`, in the form used by the cover
and the table. -/
theorem representsFPlus_of_root
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    {q : ℕ} (hq : q ∈ irregularCoefficients) (hq7 : q ≠ 7) (n p k : ℕ)
    (hp : (p : ℤ) ∈ transferPrimes) (hp2 : p ≠ 2) (hroot : LocalRoot q p (Nat.fib n % p) k)
    (hN : q * (7 * p ^ 2 / 2) ^ 2 < Nat.fib n) :
    RepresentsFPlus (q : ℤ) (Nat.fib n : ℤ) := by
  obtain ⟨hqpos, -, hres⟩ := irregularCoefficient_facts hq
  have hres' : (q : ℤ) % 7 ≠ 0 ∨ (q : ℤ) % 49 = 21 ∨ (q : ℤ) % 49 = 35 ∨
      (q : ℤ) % 49 = 42 := by omega
  obtain ⟨hqp, hk, ha⟩ := hroot
  exact representsFPlus_of_local_root hclass q (Nat.fib n) p k hres' hp hp2 hqp hk
    ha hN

/-- Proposition 6.1 from index 48: for every `q ∈ Q₇`, `f ⊥ ⟨q⟩` represents
every Fibonacci number with index at least 48. -/
theorem representsFPlus_fib_of_forty_eight_le
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    {q : ℕ} (hq : q ∈ irregularCoefficients) (n : ℕ) (hn : 48 ≤ n) :
    RepresentsFPlus (q : ℤ) (Nat.fib n : ℤ) := by
  by_cases hq7 : q = 7
  · subst q
    exact representsFPlus_seven hclass (Nat.fib n)
  obtain ⟨hqpos, hq1022, hres⟩ := irregularCoefficient_facts hq
  have hres' : (q : ℤ) % 7 ≠ 0 ∨ (q : ℤ) % 49 = 21 ∨ (q : ℤ) % 49 = 35 ∨
      (q : ℤ) % 49 = 42 := by omega
  obtain ⟨h48, h61⟩ := fib_growth_values
  rw [Nat.fastFib_eq] at h48 h61
  have hF48 : Nat.fib 48 ≤ Nat.fib n := Nat.fib_mono hn
  by_cases hbad : BadResidue q (Nat.fib n % 12)
  · have hcase : n = 57 ∨ n = 58 ∨ 61 ≤ n := by
      by_contra hcase
      have hmid := List.all_eq_true.mp middle_window_residues (n - 48)
        (List.mem_range.mpr (by omega))
      have hidx : n - 48 + 48 = n := by omega
      simp only [hidx, Nat.fastFib_eq, decide_eq_true_eq] at hmid
      unfold BadResidue at hbad
      omega
    rcases hcase with rfl | rfl | h61n
    · have hc := List.all_eq_true.mp smallPrimeTable_complete q hq
      simp only [Nat.fastFib_eq, decide_eq_true_eq] at hc
      rcases hc with h | ⟨h57 | ⟨e, he, hidx, hcoef⟩, -⟩
      · exact absurd h hq7
      · exact absurd hbad h57
      · have hcheck := List.all_eq_true.mp smallPrimeTable_checked e he
        simp only [SmallPrimeRow.check, Nat.fastFib_eq, decide_eq_true_eq] at hcheck
        obtain ⟨hp, hp2, hqp, hk, hroot, hbound⟩ := hcheck
        rw [hidx, hcoef] at hroot hbound
        rw [hcoef] at hqp
        exact representsFPlus_of_root hclass hq hq7 57 e.prime e.root hp hp2
          ⟨hqp, hk, hroot⟩ hbound
    · have hc := List.all_eq_true.mp smallPrimeTable_complete q hq
      simp only [Nat.fastFib_eq, decide_eq_true_eq] at hc
      rcases hc with h | ⟨-, h58 | ⟨e, he, hidx, hcoef⟩⟩
      · exact absurd h hq7
      · exact absurd hbad h58
      · have hcheck := List.all_eq_true.mp smallPrimeTable_checked e he
        simp only [SmallPrimeRow.check, Nat.fastFib_eq, decide_eq_true_eq] at hcheck
        obtain ⟨hp, hp2, hqp, hk, hroot, hbound⟩ := hcheck
        rw [hidx, hcoef] at hroot hbound
        rw [hcoef] at hqp
        exact representsFPlus_of_root hclass hq hq7 58 e.prime e.root hp hp2
          ⟨hqp, hk, hroot⟩ hbound
    · have hmem : q ∈ restrictedCoefficients := by
        have hc := List.all_eq_true.mp restrictedCoefficients_complete q hq
        simp only [decide_eq_true_eq] at hc
        rcases hc with h | h | h
        · exact absurd h hq7
        · unfold BadResidue at hbad
          omega
        · exact h
      rcases restricted_cover q hmem n with hgood | ⟨p, hp, k, hroot⟩
      · exact absurd hbad hgood
      · have hpc := List.all_eq_true.mp coverPrimes_checked p hp
        simp only [decide_eq_true_eq] at hpc
        obtain ⟨hpt, hp2, hpk⟩ := hpc
        have hF61 : Nat.fib 61 ≤ Nat.fib n := Nat.fib_mono h61n
        have hbound : q * (7 * p ^ 2 / 2) ^ 2 < Nat.fib n := by
          have hsq : (7 * p ^ 2 / 2) ^ 2 ≤ 41583 ^ 2 := Nat.pow_le_pow_left hpk 2
          have hmul : q * (7 * p ^ 2 / 2) ^ 2 ≤ 1022 * 41583 ^ 2 :=
            Nat.mul_le_mul hq1022 hsq
          omega
        exact representsFPlus_of_root hclass hq hq7 n p k hpt hp2 hroot hbound
  · have hsmall : 441 * (q : ℤ) < (Nat.fib n : ℤ) := by
      have : 441 * q < Nat.fib n := by omega
      exact_mod_cast this
    have hpair : ¬ BadPair (q : ℤ) (Nat.fib n : ℤ) := by
      rw [badPair_iff]
      exact hbad
    exact representsFPlus_small_subtraction hclass (q : ℤ) (Nat.fib n : ℤ)
      (by exact_mod_cast hqpos) hres' hsmall hpair

end FibonacciCriterion.Irregular
