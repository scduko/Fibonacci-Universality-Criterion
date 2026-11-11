import FibonacciCriterion.ClassicalInputs.Regular123.Mordell
import FibonacciCriterion.ClassicalInputs.Regular123.Obstruction

/-!
# The determinant-6 classification and the criterion for `⟨1,2,3⟩`

TauCeti's Minkowski reduction replaces the Mordell form of
`ClassicalInputs.Regular123.Mordell` by one of the eight reduced Gram matrices of
determinant 6 that represents the same integers, and the separator places
it in the class of `⟨1,2,3⟩`. Only representation equivalence is used, so no
change of basis from the Mordell form is needed. Induction on factors of 4
then gives `regular123_criterion`, the criterion of Proposition 3.2 for
`⟨1,2,3⟩`.
-/

namespace FibonacciCriterion.Regular123

open MordellRegularity

/-- Given `Mordell123DataSynthesis`, `⟨1,2,3⟩` represents every `m > 0` with
`4 ∤ m` and `m ≢ 10 (mod 16)`. The Mordell form represents the same integers
as a matrix of `reducedList 6` (TauCeti's reduction), and
`represents_q2_of_reduced_separator` shows that `⟨1,2,3⟩` represents them. -/
theorem represents_Q123_base_of_synthesis (S : Mordell123DataSynthesis)
    (m : ℤ) (hm : 0 < m) (hm4 : m % 4 ≠ 0) (hm16 : m % 16 ≠ 10) :
    Represents Q123 m := by
  obtain ⟨d, ha, hsep⟩ := S m hm hm4 hm16
  obtain ⟨G, hG, hrep⟩ := TernaryClassification.exists_mem_reducedList_represents_iff
    d.ternaryGram
    (by
      intro x y z hne
      rw [d.ternaryGram_eval]
      exact d.positive_of_determinant_pos hm (by norm_num) ha x y z hne)
    (D := 6) (by norm_num) (by rw [d.ternaryGram_det (ne_of_gt hm)]; norm_num)
  have hin := (hrep m).mp ((d.ternaryGram_represents_iff m).2 d.represents_input)
  have hlead := (hrep d.cxx).mp ((d.ternaryGram_represents_iff d.cxx).2 d.represents_cxx)
  obtain ⟨x, y, z, hxyz⟩ :=
    represents_q2_of_reduced_separator G d.cxx m hG hlead hsep hin
  exact ⟨x, y, z, by simpa [q2Gram, TernaryGram.eval, Q123] using hxyz⟩

/-- Given `Mordell123DataSynthesis`, `⟨1,2,3⟩` represents every positive
natural number outside the exceptional set, by induction on factors of 4. -/
theorem represents_Q123_nat_of_synthesis (S : Mordell123DataSynthesis) :
    ∀ n : ℕ, 0 < n → ¬ ClassicalRepresentation.Exceptional123 (n : ℤ) →
      Represents Q123 (n : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn hnot
      by_cases h4 : n % 4 = 0
      · obtain ⟨k, rfl⟩ := Nat.dvd_iff_mod_eq_zero.mpr h4
        have hk : 0 < k := by omega
        have hklt : k < 4 * k := by omega
        have hnotk : ¬ ClassicalRepresentation.Exceptional123 (k : ℤ) := by
          rintro ⟨a, b, hkb⟩
          apply hnot
          refine ⟨a + 1, b, ?_⟩
          push_cast
          rw [hkb, pow_succ]
          ring
        obtain ⟨x, y, z, hxyz⟩ := ih k hklt hk hnotk
        refine ⟨2 * x, 2 * y, 2 * z, ?_⟩
        dsimp [Q123] at hxyz ⊢
        nlinarith
      · have hm4 : ((n : ℤ) % 4) ≠ 0 := by exact_mod_cast h4
        have h16 : n % 16 ≠ 10 := by
          intro h16
          apply hnot
          refine ⟨0, ((n / 16 : ℕ) : ℤ), ?_⟩
          simp only [pow_zero, one_mul]
          omega
        exact represents_Q123_base_of_synthesis S (n : ℤ)
          (by exact_mod_cast hn) hm4 (by exact_mod_cast h16)

/-- The same conclusion from `Mordell123CongruenceRows`. -/
theorem represents_Q123_nat_of_arithmetic (C : Mordell123CongruenceRows) :
    ∀ n : ℕ, 0 < n → ¬ ClassicalRepresentation.Exceptional123 (n : ℤ) →
      Represents Q123 (n : ℤ) :=
  represents_Q123_nat_of_synthesis (dataSynthesis_of_congruence_rows C)

/-- Given `Mordell123CongruenceRows`, a nonnegative integer is represented by
`⟨1,2,3⟩` if and only if it lies outside the exceptional set. Necessity is
`represents123_implies_not_exceptional`. -/
theorem regular123_criterion_of_arithmetic (C : Mordell123CongruenceRows)
    (n : ℤ) (hn : 0 ≤ n) :
    ClassicalRepresentation.Represents123 n ↔
      ¬ ClassicalRepresentation.Exceptional123 n := by
  constructor
  · exact ClassicalRepresentation.represents123_implies_not_exceptional
  · intro hnot
    by_cases hzero : n = 0
    · subst n
      exact ⟨0, 0, 0, by norm_num⟩
    have hnat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    have hpos : 0 < n.toNat := by omega
    have hrep := represents_Q123_nat_of_arithmetic C n.toNat hpos (by rw [hnat]; exact hnot)
    simpa only [Represents, Q123, hnat,
      ClassicalRepresentation.Represents123] using hrep

/-- The same criterion from `EvenMordell123CongruenceRows`; the odd residue
families come from `oddInputCongruenceRow`. -/
theorem regular123_criterion_of_evenArithmetic (E : EvenMordell123CongruenceRows)
    (n : ℤ) (hn : 0 ≤ n) :
    ClassicalRepresentation.Represents123 n ↔
      ¬ ClassicalRepresentation.Exceptional123 n :=
  regular123_criterion_of_arithmetic (congruenceRows_of_even E) n hn

/-- Proposition 3.2 for `⟨1,2,3⟩`: a nonnegative integer `n` is represented
by `⟨1,2,3⟩` if and only if `n` is not of the form `4^a (16b + 10)`. The
manuscript cites Jones–Pall for sufficiency; here the proof uses the Mordell
construction and the classification at determinant 6. -/
theorem regular123_criterion (n : ℤ) (hn : 0 ≤ n) :
    ClassicalRepresentation.Represents123 n ↔
      ¬ ClassicalRepresentation.Exceptional123 n :=
  regular123_criterion_of_evenArithmetic evenMordell123CongruenceRows n hn

end FibonacciCriterion.Regular123
