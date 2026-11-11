import FibonacciCriterion.ClassicalInputs.ThreeSquares.Obstruction
import FibonacciCriterion.ClassicalInputs.Regular113.Obstruction
import FibonacciCriterion.ClassicalInputs.Mordell
import FibonacciCriterion.ClassicalInputs.Regular113.ResidueRows
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Sufficiency for `⟨1,1,3⟩`: the Mordell construction

This file proves the sufficiency direction of the criterion of Proposition 3.2
for `⟨1,1,3⟩`, assuming the classification of positive ternaries of
determinant 3 (`regular113Sufficiency_of_classification`). The manuscript
cites Jones–Pall; here the proof follows the Mordell construction of
Blackwell–Durham–Thompson–Treece.

For positive `m` with `4 ∤ m`, `9 ∤ m`, and `m ≢ 6 (mod 9)`, Dirichlet's
theorem and Jacobi reciprocity give a positive-definite Mordell form of
determinant 3 that represents `m` and has leading coefficient `≡ 5 (mod 8)`
(`mordell113Witnesses`, `mordell113Construction_of_witnesses`). The second
class `Q113Other` omits that residue, so the form represents the same integers
as `⟨1,1,3⟩`. Descent by 4 and 9 extends this to every nonnegative integer
outside the exceptional set.
`ClassicalInputs.Regular113.Classification` proves the classification.
-/

namespace FibonacciCriterion.MordellRegularity

open ClassicalRepresentation

/-! ## The second determinant-3 class -/

/-- The form `x² + 2y² + 2yz + 2z²`, the second class of positive-definite
ternary forms of determinant 3 with integral symmetric Gram matrix. -/
def Q113Other : TernaryForm :=
  fun x y z ↦ x ^ 2 + 2 * y ^ 2 + 2 * y * z + 2 * z ^ 2

/-- Two ternary forms are representation-equivalent if they represent the same
integers. The Mordell argument uses nothing more of an integral equivalence. -/
def RepresentationEquivalent (Q R : TernaryForm) : Prop :=
  ∀ n : ℤ, Represents Q n ↔ Represents R n

/-- Twice the Eisenstein norm `y² + yz + z²` is 0, 2, or 6 modulo 8. -/
theorem twice_eisenstein_norm_mod_eight (y z : ℤ) :
    (2 * (y ^ 2 + y * z + z ^ 2)) % 8 = 0 ∨
      (2 * (y ^ 2 + y * z + z ^ 2)) % 8 = 2 ∨
      (2 * (y ^ 2 + y * z + z ^ 2)) % 8 = 6 := by
  have hnorm :
      (y ^ 2 + y * z + z ^ 2) % 4 = 0 ∨
        (y ^ 2 + y * z + z ^ 2) % 4 = 1 ∨
        (y ^ 2 + y * z + z ^ 2) % 4 = 3 := by
    have hy0 : 0 ≤ y % 4 := Int.emod_nonneg _ (by norm_num)
    have hy4 : y % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    have hz0 : 0 ≤ z % 4 := Int.emod_nonneg _ (by norm_num)
    have hz4 : z % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases hy : y % 4 <;> interval_cases hz : z % 4 <;>
      norm_num [pow_two, Int.add_emod, Int.mul_emod, hy, hz]
  rcases hnorm with hnorm | hnorm | hnorm <;> omega

/-- `Q113Other` represents no integer `≡ 5 (mod 8)`. -/
theorem not_Q113Other_represents_mod_eight (n : ℤ) (hn : n % 8 = 5) :
    ¬ Represents Q113Other n := by
  rintro ⟨x, y, z, h⟩
  have hm := congrArg (fun t : ℤ => t % 8) h
  have hrewrite :
      x ^ 2 + 2 * y ^ 2 + 2 * y * z + 2 * z ^ 2 =
        x ^ 2 + 2 * (y ^ 2 + y * z + z ^ 2) := by ring
  change (x ^ 2 + 2 * y ^ 2 + 2 * y * z + 2 * z ^ 2) % 8 = n % 8 at hm
  rw [hrewrite] at hm
  rcases RegularReductions.square_mod_eight x with hx | hx | hx <;>
    rcases twice_eisenstein_norm_mod_eight y z with hyz | hyz | hyz <;>
    norm_num [Int.add_emod, hx, hyz, hn] at hm

/-- For `3 ∤ m` and a row of the unramified table, the Chinese remainder
theorem gives a residue `R` prime to `24m` with
`R ≡ unramified113Residue m A (mod 8m)` and `R ≡ 1 (mod 3)`. -/
theorem exists_unramified113_crt_residue {m A α : ℕ} (hm : 0 < m)
    (h3 : ¬ 3 ∣ m) (hrow : IsUnramified113Row m A α) :
    ∃ R : ℕ, R.Coprime ((8 * m) * 3) ∧
      R ≡ unramified113Residue m A [MOD 8 * m] ∧ R ≡ 1 [MOD 3] := by
  have hm3 : m.Coprime 3 := by
    rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
    exact h3
  have hq3 : (8 * m).Coprime 3 := by
    exact (by norm_num : Nat.Coprime 8 3).mul_left hm3
  let R := Nat.chineseRemainder hq3 (unramified113Residue m A) 1
  have hRq : (R : ℕ).Coprime (8 * m) :=
    coprime_of_modEq R.prop.1 (unramified113_residue_coprime hm h3 hrow)
  have hR3 : (R : ℕ).Coprime 3 := coprime_of_modEq R.prop.2 (by norm_num)
  exact ⟨R, hRq.mul_right hR3, R.prop.1, R.prop.2⟩

/-- For `3 ∤ m`, Dirichlet's theorem gives an auxiliary prime `p > 3m` in the
class of `exists_unramified113_crt_residue`. Writing
`p = unramified113Residue m A + 8mk`, it satisfies the separator identity
`A² + p = m(8(A² + k) + 5)`. -/
theorem exists_unramified113_auxiliary_prime {m A α : ℕ} (hm : 0 < m)
    (h3 : ¬ 3 ∣ m) (hrow : IsUnramified113Row m A α) :
    ∃ p k : ℕ, 3 * m < p ∧ p.Prime ∧
      p = unramified113Residue m A + (8 * m) * k ∧
      p ≡ unramified113Residue m A [MOD 8 * m] ∧
      p ≡ 1 [MOD 3] ∧ A ^ 2 + p = m * (8 * (A ^ 2 + k) + 5) := by
  obtain ⟨R, hRcop, hR8, hR3⟩ :=
    exists_unramified113_crt_residue hm h3 hrow
  obtain ⟨p, hrp, hp, hpR⟩ :=
    exists_auxiliary_prime (max (unramified113Residue m A) (3 * m))
      ((8 * m) * 3) R (by positivity) hRcop
  have hp8 : p ≡ unramified113Residue m A [MOD 8 * m] :=
    (hpR.of_dvd (by exact dvd_mul_right (8 * m) 3)).trans hR8
  have hp3 : p ≡ 1 [MOD 3] :=
    (hpR.of_dvd (by exact dvd_mul_left 3 (8 * m))).trans hR3
  have hres_lt : unramified113Residue m A < p :=
    (le_max_left _ _).trans_lt hrp
  have h3m_lt : 3 * m < p := (le_max_right _ _).trans_lt hrp
  have hdiv : 8 * m ∣ p - unramified113Residue m A :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hres_lt)).mp hp8.symm
  obtain ⟨k, hk⟩ := hdiv
  have hpk : p = unramified113Residue m A + (8 * m) * k := by omega
  exact ⟨p, k, h3m_lt, hp, hpk, hp8, hp3,
    unramified113_prime_separator hm hrow hpk⟩

/-- In the ramified case, Dirichlet's theorem gives an auxiliary prime
`p > m₁` with `p = ramified113Residue m₁ A₀ + 8m₁k`, and then
`3A₀² + p = m₁(8(A₀² + k) + 5)`. No condition modulo 3 is needed. -/
theorem exists_ramified113_auxiliary_prime {m₁ A₀ α : ℕ} (hm₁ : 0 < m₁)
    (h3 : ¬ 3 ∣ m₁) (hrow : IsRamified113Row m₁ A₀ α) :
    ∃ p k : ℕ, m₁ < p ∧ p.Prime ∧
      p = ramified113Residue m₁ A₀ + (8 * m₁) * k ∧
      p ≡ ramified113Residue m₁ A₀ [MOD 8 * m₁] ∧
      3 * A₀ ^ 2 + p = m₁ * (8 * (A₀ ^ 2 + k) + 5) := by
  obtain ⟨p, hmp, hp, hmod⟩ :=
    exists_auxiliary_prime (max (ramified113Residue m₁ A₀) m₁)
      (8 * m₁) (ramified113Residue m₁ A₀) (by positivity)
      (ramified113_residue_coprime hm₁ h3 hrow)
  have hres_lt : ramified113Residue m₁ A₀ < p :=
    (le_max_left _ _).trans_lt hmp
  have hm_lt : m₁ < p := (le_max_right _ _).trans_lt hmp
  have hdiv : 8 * m₁ ∣ p - ramified113Residue m₁ A₀ :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hres_lt)).mp hmod.symm
  obtain ⟨k, hk⟩ := hdiv
  have hpk : p = ramified113Residue m₁ A₀ + (8 * m₁) * k := by omega
  exact ⟨p, k, hm_lt, hp, hpk, hmod,
    ramified113_prime_separator hm₁ hrow hpk⟩

/-! ## Reciprocity and the Mordell data -/

/-- For odd `m` and `p` with `p ≡ m (mod 4)`, the Jacobi symbols satisfy
`(-m/p) = (p/m)`. -/
theorem jacobi_neg_swap_of_same_mod_four {m p : ℕ}
    (hm : Odd m) (hp : Odd p) (h4 : p % 4 = m % 4) :
    jacobiSym (-(m : ℤ)) p = jacobiSym (p : ℤ) m := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with hm4 | hm4
  · have hp4 : p % 4 = 1 := h4.trans hm4
    rw [jacobiSym.neg _ hp, ZMod.χ₄_nat_one_mod_four hp4,
      jacobiSym.quadratic_reciprocity_one_mod_four hm4 hp, one_mul]
  · have hp4 : p % 4 = 3 := h4.trans hm4
    rw [jacobiSym.neg _ hp, ZMod.χ₄_nat_three_mod_four hp4,
      jacobiSym.quadratic_reciprocity_three_mod_four hm4 hp4]
    ring

/-- For odd `m ≡ 1 (mod 3)`, `(-3/m) = 1`. -/
theorem jacobi_neg_three_eq_one {m : ℕ} (hm : Odd m) (h3 : m % 3 = 1) :
    jacobiSym (-3) m = 1 := by
  rw [jacobi_neg_three_swap hm, jacobiSym.mod_left]
  have h3z : (m : ℤ) % 3 = 1 := by exact_mod_cast h3
  exact (congrArg (fun z : ℤ => jacobiSym z 3) h3z).trans (by norm_num)

/-- The reciprocity condition of the unramified case: for `m > 0` with
`3 ∤ m`, a row of `IsUnramified113Row`, and a prime
`p ≡ unramified113Residue m A (mod 8m)` with `p ≡ 1 (mod 3)`, `-3m` is a
nonzero square modulo `p`. It is proven as `unramified113Reciprocity`. -/
def Unramified113Reciprocity : Prop :=
  ∀ m A α p : ℕ, 0 < m → ¬ 3 ∣ m → IsUnramified113Row m A α →
    ∀ hp : p.Prime, p ≡ unramified113Residue m A [MOD 8 * m] →
      p ≡ 1 [MOD 3] → @legendreSym p ⟨hp⟩ (-(3 * (m : ℤ))) = 1

/-- `Unramified113Reciprocity` for odd `m` (the four odd rows). The square
`A²` in the separator identity gives `(-m/p) = (-1/m)`, so
`(m/p) = 1`; and `(-3/p) = 1` since `p ≡ 1 (mod 3)`. -/
theorem unramified113_reciprocity_of_odd {m A α p : ℕ}
    (hm : 0 < m) (hodd : Odd m) (h3 : ¬ 3 ∣ m)
    (hrow : IsUnramified113Row m A α) (hp : p.Prime)
    (hpr : p ≡ unramified113Residue m A [MOD 8 * m])
    (hp3 : p ≡ 1 [MOD 3]) :
    @legendreSym p ⟨hp⟩ (-(3 * (m : ℤ))) = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hodd
  have hp8 : p % 8 = α % 8 :=
    (hpr.of_dvd (dvd_mul_right 8 m)).trans
      (unramified113_residue_mod_eight hm hrow)
  have hpodd : Odd p := by
    apply Nat.odd_iff.mpr
    rcases hrow with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, rfl⟩ <;> norm_num at hp8 <;> omega
  have h4 : p % 4 = m % 4 := by
    rcases hrow with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, rfl⟩ <;> norm_num at hp8 <;> omega
  have hpm := hpr.of_dvd (dvd_mul_left m 8)
  have hid := unramified113_residue_identity hm hrow
  have hsquare : jacobiSym ((A : ℤ) ^ 2) m = 1 := by
    apply jacobiSym.sq_one'
    simpa only [Int.gcd_natCast_natCast] using
      (unramified113_row_coprime h3 hrow).symm
  have hswap : jacobiSym (-(m : ℤ)) p = ZMod.χ₄ m := by
    rw [jacobi_neg_swap_of_same_mod_four hodd hpodd h4,
      jacobi_of_separator_residue hpm hid, Nat.cast_pow,
      jacobiSym.neg _ hodd, hsquare, mul_one]
  have hchar : ZMod.χ₄ p = ZMod.χ₄ m := by
    rw [ZMod.χ₄_nat_mod_four, ZMod.χ₄_nat_mod_four m, h4]
  have hmleg : jacobiSym (m : ℤ) p = 1 := by
    rw [jacobiSym.neg _ hpodd, hchar] at hswap
    rcases Nat.odd_mod_four_iff.mp hm2 with hm4 | hm4
    · rw [ZMod.χ₄_nat_one_mod_four hm4] at hswap
      simpa using hswap
    · rw [ZMod.χ₄_nat_three_mod_four hm4] at hswap
      linarith
  rw [jacobiSym.legendreSym.to_jacobiSym,
    show -(3 * (m : ℤ)) = (-3) * (m : ℤ) by ring,
    jacobiSym.mul_left, hmleg, mul_one]
  exact jacobi_neg_three_eq_one hpodd (by simpa [Nat.ModEq] using hp3)

/-- Given `Unramified113Reciprocity`, every `m > 0` with `4 ∤ m` and `3 ∤ m`
has integers `a > 0`, `A`, `s`, `t`, `C` with `A² + a = m(8C + 5)` and
`as - 3mt² = 1`. Here `a` is the auxiliary prime. -/
theorem exists_unramified113_witnesses
    (hrec : Unramified113Reciprocity) {m : ℕ} (hm : 0 < m)
    (h4 : ¬ 4 ∣ m) (h3 : ¬ 3 ∣ m) :
    ∃ a A s t C : ℤ, 0 < a ∧
      A ^ 2 + a = (m : ℤ) * (8 * C + 5) ∧
      a * s - 3 * (m : ℤ) * t ^ 2 = 1 := by
  obtain ⟨A, α, hrow⟩ := exists_unramified113_row m h4
  obtain ⟨p, k, h3mp, hp, hpk, hp8, hp3, hsep⟩ :=
    exists_unramified113_auxiliary_prime hm h3 hrow
  let _ : Fact p.Prime := ⟨hp⟩
  have hleg : legendreSym p (-(3 * (m : ℤ))) = 1 :=
    hrec m A α p hm h3 hrow hp hp8 hp3
  have hd : (((3 * (m : ℕ) : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvdz : (p : ℤ) ∣ ((3 * m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hdvd : p ∣ 3 * m := by exact_mod_cast hdvdz
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) h3mp) hdvd
  obtain ⟨s, t, hst⟩ :=
    exists_binary_unit_completion_of_legendre (d := 3 * m) (p := p)
      hd (by simpa using hleg)
  refine ⟨(p : ℤ), (A : ℤ), s, t, (A ^ 2 + k : ℕ), ?_, ?_, ?_⟩
  · exact_mod_cast hp.pos
  · exact_mod_cast hsep
  · simpa [Nat.cast_mul] using hst

/-- The reciprocity condition of the ramified case `m = 3m₁`: for `m₁ > 0`
with `m₁ ≡ 1 (mod 3)`, a row of `IsRamified113Row`, and a prime
`p ≡ ramified113Residue m₁ A₀ (mod 8m₁)`, `-m₁` is a nonzero square modulo
`p`. The condition `m₁ ≡ 1 (mod 3)` is needed: `m₁ ≡ 2 (mod 3)` gives the
exceptional inputs `m ≡ 6 (mod 9)`. -/
def Ramified113Reciprocity : Prop :=
  ∀ m₁ A₀ α p : ℕ, 0 < m₁ → m₁ % 3 = 1 → IsRamified113Row m₁ A₀ α →
    ∀ hp : p.Prime, p ≡ ramified113Residue m₁ A₀ [MOD 8 * m₁] →
      @legendreSym p ⟨hp⟩ (-(m₁ : ℤ)) = 1

/-- `Ramified113Reciprocity` for odd `m₁` (the four odd rows). -/
theorem ramified113_reciprocity_of_odd {m₁ A₀ α p : ℕ}
    (hm₁ : 0 < m₁) (hodd : Odd m₁) (h3 : m₁ % 3 = 1)
    (hrow : IsRamified113Row m₁ A₀ α) (hp : p.Prime)
    (hpr : p ≡ ramified113Residue m₁ A₀ [MOD 8 * m₁]) :
    @legendreSym p ⟨hp⟩ (-(m₁ : ℤ)) = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hm2 : m₁ % 2 = 1 := Nat.odd_iff.mp hodd
  have hp8 : p % 8 = α % 8 :=
    (hpr.of_dvd (dvd_mul_right 8 m₁)).trans
      (ramified113_residue_mod_eight hm₁ hrow)
  have hA : A₀ = 2 := by
    rcases hrow with h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, hα⟩ <;> omega
  have hpodd : Odd p := by
    apply Nat.odd_iff.mpr
    rcases hrow with h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, rfl⟩ <;> norm_num at hp8 <;> omega
  have h4 : p % 4 = m₁ % 4 := by
    rcases hrow with h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, rfl⟩ <;> norm_num at hp8 <;> omega
  rw [jacobiSym.legendreSym.to_jacobiSym,
    jacobi_neg_swap_of_same_mod_four hodd hpodd h4]
  have hpm := hpr.of_dvd (dvd_mul_left m₁ 8)
  have hid := ramified113_residue_identity hm₁ hrow
  rw [jacobi_of_separator_residue hpm hid, hA]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (-(3 * (2 : ℤ) ^ 2)) = (-3) * 4 by norm_num,
    jacobiSym.mul_left, jacobi_neg_three_eq_one hodd h3,
    jacobiSym.at_four hodd, mul_one]

/-- Given `Ramified113Reciprocity`, every `m₁ > 0` with `4 ∤ m₁` and
`m₁ ≡ 1 (mod 3)` has integers `a₁ > 0`, `A`, `s`, `t`, `C` with
`A² + 3a₁ = 3m₁(8C + 5)` and `a₁s - m₁t² = 1`. Here `a₁` is the auxiliary
prime and `A = 3A₀`. -/
theorem exists_ramified113_witnesses
    (hrec : Ramified113Reciprocity) {m₁ : ℕ} (hm₁ : 0 < m₁)
    (h4 : ¬ 4 ∣ m₁) (hmod3 : m₁ % 3 = 1) :
    ∃ a₁ A s t C : ℤ, 0 < a₁ ∧
      A ^ 2 + 3 * a₁ = ((3 * m₁ : ℕ) : ℤ) * (8 * C + 5) ∧
      a₁ * s - (m₁ : ℤ) * t ^ 2 = 1 := by
  have h3 : ¬ 3 ∣ m₁ := by
    simp [Nat.dvd_iff_mod_eq_zero, hmod3]
  obtain ⟨A₀, α, hrow⟩ := exists_ramified113_row m₁ h4
  obtain ⟨p, k, hm₁p, hp, hpk, hp8, hsep⟩ :=
    exists_ramified113_auxiliary_prime hm₁ h3 hrow
  let _ : Fact p.Prime := ⟨hp⟩
  have hleg : legendreSym p (-(m₁ : ℤ)) = 1 :=
    hrec m₁ A₀ α p hm₁ hmod3 hrow hp hp8
  have hd : (((m₁ : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvdz : (p : ℤ) ∣ (m₁ : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hdvd : p ∣ m₁ := by exact_mod_cast hdvdz
    exact (Nat.not_dvd_of_pos_of_lt hm₁ hm₁p) hdvd
  obtain ⟨s, t, hst⟩ :=
    exists_binary_unit_completion_of_legendre (d := m₁) (p := p) hd hleg
  refine ⟨(p : ℤ), (3 * A₀ : ℕ), s, t, (A₀ ^ 2 + k : ℕ), ?_, ?_, ?_⟩
  · exact_mod_cast hp.pos
  · have hsepz :
        (3 : ℤ) * (A₀ : ℤ) ^ 2 + (p : ℤ) =
          (m₁ : ℤ) * (8 * ((A₀ ^ 2 + k : ℕ) : ℤ) + 5) := by
      exact_mod_cast hsep
    calc
      ((3 * A₀ : ℕ) : ℤ) ^ 2 + 3 * (p : ℤ) =
          3 * ((3 : ℤ) * (A₀ : ℤ) ^ 2 + (p : ℤ)) := by
            push_cast
            ring
      _ = 3 * ((m₁ : ℤ) * (8 * ((A₀ ^ 2 + k : ℕ) : ℤ) + 5)) := by
            rw [hsepz]
      _ = ((3 * m₁ : ℕ) : ℤ) * (8 * ((A₀ ^ 2 + k : ℕ) : ℤ) + 5) := by
            push_cast
            ring
  · simpa using hst

/-- The Mordell construction for `⟨1,1,3⟩`: every `m > 0` with `4 ∤ m`,
`9 ∤ m`, and `m ≢ 6 (mod 9)` has a Mordell datum of determinant 3 with
`a > 0` and leading coefficient `cxx ≡ 5 (mod 8)`. -/
def Mordell113Construction : Prop :=
  ∀ m : ℕ, 0 < m → ¬ 4 ∣ m → ¬ 9 ∣ m → ((m : ℤ) % 9 ≠ 6) →
    ∃ d : MordellDatum (m : ℤ) 3,
      0 < d.a ∧ d.cxx % 8 = 5

/-- The integer data of the Mordell construction for `⟨1,1,3⟩`, for the
inputs of `Mordell113Construction`. The first disjunct is the binary
completion for `3 ∤ m`, with `h = 3mt` and `b = 3ms`. The second is the case
`3 ∣ m`: write `m = 3m₁`, `a = 3a₁`, `h = mt`, and `b = ms`. In both cases the
first equation makes the leading coefficient an integer `≡ 5 (mod 8)`. -/
def Mordell113Witnesses : Prop :=
  ∀ m : ℕ, 0 < m → ¬ 4 ∣ m → ¬ 9 ∣ m → ((m : ℤ) % 9 ≠ 6) →
    (∃ a A s t C : ℤ,
        0 < a ∧ A ^ 2 + a = (m : ℤ) * (8 * C + 5) ∧
          a * s - 3 * (m : ℤ) * t ^ 2 = 1) ∨
      (∃ m₁ : ℕ, ∃ a₁ A s t C : ℤ,
        m = 3 * m₁ ∧ 0 < a₁ ∧
          A ^ 2 + 3 * a₁ = (m : ℤ) * (8 * C + 5) ∧
          a₁ * s - (m₁ : ℤ) * t ^ 2 = 1)

/-- The two reciprocity conditions imply `Mordell113Witnesses`. The case
`3 ∤ m` uses the unramified table. In the case `m = 3m₁`, the conditions
`9 ∤ m` and `m ≢ 6 (mod 9)` give `m₁ ≡ 1 (mod 3)`, and the ramified table
applies. -/
theorem mordell113Witnesses_of_reciprocity
    (hun : Unramified113Reciprocity) (hram : Ramified113Reciprocity) :
    Mordell113Witnesses := by
  intro m hm h4 h9 h6
  by_cases h3 : 3 ∣ m
  · obtain ⟨m₁, rfl⟩ := h3
    have hm₁ : 0 < m₁ := by omega
    have h4m₁ : ¬ 4 ∣ m₁ := by
      rintro ⟨k, rfl⟩
      apply h4
      refine ⟨3 * k, ?_⟩
      ring
    have h3m₁ : ¬ 3 ∣ m₁ := by
      rintro ⟨k, rfl⟩
      apply h9
      refine ⟨k, ?_⟩
      ring
    have hmod3 : m₁ % 3 = 1 := by
      have hmod_ne : m₁ % 3 ≠ 0 := by
        simpa [Nat.dvd_iff_mod_eq_zero] using h3m₁
      have hmod6 : (3 * m₁) % 9 ≠ 6 := by exact_mod_cast h6
      omega
    obtain ⟨a₁, A, s, t, C, ha₁, hsep, hst⟩ :=
      exists_ramified113_witnesses hram hm₁ h4m₁ hmod3
    exact Or.inr ⟨m₁, a₁, A, s, t, C, rfl, ha₁, hsep, hst⟩
  · obtain ⟨a, A, s, t, C, ha, hsep, hst⟩ :=
      exists_unramified113_witnesses hun hm h4 h3
    exact Or.inl ⟨a, A, s, t, C, ha, hsep, hst⟩

/-- The integer data of `Mordell113Witnesses` give the Mordell data of
`Mordell113Construction`, with `B = 0` (`MordellDatum.ofBZero`). -/
theorem mordell113Construction_of_witnesses
    (hw : Mordell113Witnesses) : Mordell113Construction := by
  intro m hm h4 h9 h6
  rcases hw m hm h4 h9 h6 with hcoprime | hramified
  · obtain ⟨a, A, s, t, C, ha, hA, hast⟩ := hcoprime
    have hdetmul := congrArg (fun q : ℤ => 3 * (m : ℤ) * q) hast
    let d : MordellDatum (m : ℤ) 3 :=
      MordellDatum.ofBZero
        (A := A) (a := a) (h := 3 * (m : ℤ) * t)
        (b := 3 * (m : ℤ) * s) (cxx := 8 * C + 5)
        (cxy := 3 * t) (cyy := 3 * s)
        hA (by ring) (by ring) (by nlinarith [hdetmul])
    refine ⟨d, ha, ?_⟩
    change (8 * C + 5) % 8 = 5
    omega
  · obtain ⟨m₁, a₁, A, s, t, C, hm₁, ha₁, hA, hast⟩ := hramified
    have hm₁z : (m : ℤ) = 3 * (m₁ : ℤ) := by exact_mod_cast hm₁
    let d : MordellDatum (m : ℤ) 3 :=
      MordellDatum.ofBZero
        (A := A) (a := 3 * a₁) (h := (m : ℤ) * t)
        (b := (m : ℤ) * s) (cxx := 8 * C + 5)
        (cxy := t) (cyy := s)
        hA (by ring) (by ring) (by
          calc
            3 * a₁ * ((m : ℤ) * s) - ((m : ℤ) * t) ^ 2 =
                9 * (m₁ : ℤ) * (a₁ * s - (m₁ : ℤ) * t ^ 2) := by
                  rw [hm₁z]
                  ring
            _ = 9 * (m₁ : ℤ) := by rw [hast]; ring
            _ = 3 * (m : ℤ) := by rw [hm₁z]; ring)
    refine ⟨d, mul_pos (by norm_num) ha₁, ?_⟩
    change (8 * C + 5) % 8 = 5
    omega

/-- The classification hypothesis: the form of a positive-definite Mordell
datum of determinant 3 is representation-equivalent to `Q113` or
`Q113Other`. `ClassicalInputs.Regular113.Classification` proves it by TauCeti reduction and the
checked list of reduced Gram matrices. -/
def DeterminantThreeClassification : Prop :=
  ∀ {m : ℤ} (_hm : m ≠ 0) (d : MordellDatum m 3),
    PositiveTernary d.form →
      RepresentationEquivalent d.form Q113 ∨
        RepresentationEquivalent d.form Q113Other

/-- Given the classification, a positive-definite Mordell datum of
determinant 3 with `cxx ≡ 5 (mod 8)` shows that `⟨1,1,3⟩` represents `m`:
the form represents `cxx`, which `Q113Other` omits. -/
theorem represents_Q113_of_mordell_data
    (hclass : DeterminantThreeClassification)
    {m : ℕ} (hm : 0 < m) (d : MordellDatum (m : ℤ) 3)
    (hpos : PositiveTernary d.form) (hsep : d.cxx % 8 = 5) :
    Represents Q113 (m : ℤ) := by
  rcases hclass (by exact_mod_cast (ne_of_gt hm)) d hpos with htarget | hother
  · exact (htarget (m : ℤ)).mp d.represents_input
  · exfalso
    exact not_Q113Other_represents_mod_eight d.cxx hsep
      ((hother d.cxx).mp d.represents_cxx)

/-- The Mordell construction and the classification show that `⟨1,1,3⟩`
represents every `m > 0` with `4 ∤ m`, `9 ∤ m`, and `m ≢ 6 (mod 9)`. -/
theorem normalized_sufficiency_of_mordell
    (hconstruct : Mordell113Construction)
    (hclass : DeterminantThreeClassification) :
    ∀ m : ℕ, 0 < m → ¬ 4 ∣ m → ¬ 9 ∣ m → ((m : ℤ) % 9 ≠ 6) →
      Represents113 (m : ℤ) := by
  intro m hm h4 h9 h6
  obtain ⟨d, ha, hsep⟩ := hconstruct m hm h4 h9 h6
  have hpos := d.positive_of_determinant_pos (by exact_mod_cast hm) (by norm_num) ha
  simpa [Q113, Represents, Represents113] using
    represents_Q113_of_mordell_data hclass hm d hpos hsep

/-! ## Removing factors of 4 and 9 -/

/-- If `⟨1,1,3⟩` represents `n`, it represents `4n`. -/
theorem represents113_four_mul {n : ℤ} (h : Represents113 n) :
    Represents113 (4 * n) := by
  have h' := RegularReductions.diagonal_square_scale 1 1 3 n 2
    (by simpa only [Represents113, one_mul] using h)
  simpa only [Represents113, one_mul, show (2 : ℤ) ^ 2 = 4 by norm_num] using h'

/-- If `⟨1,1,3⟩` represents every `m > 0` with `4 ∤ m`, `9 ∤ m`, and
`m ≢ 6 (mod 9)`, then `Regular113Sufficiency` holds. The proof removes factors
of 4 and 9 by strong induction and does not use the Mordell
construction. -/
theorem regular113Sufficiency_of_normalized
    (hbase : ∀ m : ℕ, 0 < m → ¬ 4 ∣ m → ¬ 9 ∣ m → ((m : ℤ) % 9 ≠ 6) →
      Represents113 (m : ℤ)) :
    Regular113.Regular113Sufficiency := by
  have hall : ∀ m : ℕ,
      ¬ ClassicalRepresentation.Exceptional113 (m : ℤ) →
        Represents113 (m : ℤ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hnot
        by_cases hm0 : m = 0
        · subst m
          exact ⟨0, 0, 0, by norm_num⟩
        have hm : 0 < m := Nat.pos_of_ne_zero hm0
        by_cases h9 : 9 ∣ m
        · obtain ⟨k, rfl⟩ := h9
          have hk : 0 < k := by omega
          have hlt : k < 9 * k := by omega
          have hnotk :
              ¬ ClassicalRepresentation.Exceptional113 (k : ℤ) := by
            rintro ⟨a, b, hab⟩
            apply hnot
            refine ⟨a + 1, b, ?_⟩
            push_cast
            rw [hab, pow_succ]
            ring
          have hrep := ih k hlt hnotk
          have hscaled :=
            (Regular113.represents113_nine_mul_iff (k : ℤ)).2 hrep
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hscaled
        · by_cases h4 : 4 ∣ m
          · obtain ⟨k, rfl⟩ := h4
            have hk : 0 < k := by omega
            have hlt : k < 4 * k := by omega
            have hnotk :
                ¬ ClassicalRepresentation.Exceptional113 (k : ℤ) := by
              rintro ⟨a, b, hab⟩
              apply hnot
              refine ⟨a, 4 * b + 2, ?_⟩
              push_cast
              rw [hab]
              ring
            have hrep := ih k hlt hnotk
            have hscaled := represents113_four_mul hrep
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using hscaled
          · have h6 : ((m : ℤ) % 9 ≠ 6) := by
              intro hmod
              apply hnot
              refine ⟨0, (m : ℤ) / 9, ?_⟩
              simp only [pow_zero, one_mul]
              omega
            exact hbase m hm h4 h9 h6
  intro n hn hnot
  by_cases hn0 : n = 0
  · subst n
    exact ⟨0, 0, 0, by norm_num⟩
  let m := n.toNat
  have hmcast : (m : ℤ) = n := by
    dsimp [m]
    simpa using Int.toNat_of_nonneg hn
  rw [← hmcast] at hnot ⊢
  exact hall m hnot

/-- The Mordell construction and the classification imply
`Regular113Sufficiency`. -/
theorem regular113Sufficiency_of_mordell
    (hconstruct : Mordell113Construction)
    (hclass : DeterminantThreeClassification) :
    Regular113.Regular113Sufficiency :=
  regular113Sufficiency_of_normalized
    (normalized_sufficiency_of_mordell hconstruct hclass)

/-- `Mordell113Witnesses` and the classification imply
`Regular113Sufficiency`. -/
theorem regular113Sufficiency_of_witnesses
    (hw : Mordell113Witnesses)
    (hclass : DeterminantThreeClassification) :
    Regular113.Regular113Sufficiency :=
  regular113Sufficiency_of_mordell
    (mordell113Construction_of_witnesses hw) hclass

/-! ## Even inputs

An even input not divisible by 4 is `2n` with `n` odd. Writing it so
separates the supplementary law at 2, and the rows are chosen so that its
sign cancels the sign from reciprocity. The Jacobi symbol is used at the
composite `n`, so `n` is not factored.
-/

/-- `Unramified113Reciprocity` for even `m` (the four even rows). -/
theorem unramified113_reciprocity_of_even {m A α p : ℕ}
    (hm : 0 < m) (heven : m % 2 = 0) (h3 : ¬ 3 ∣ m)
    (hrow : IsUnramified113Row m A α) (hp : p.Prime)
    (hpr : p ≡ unramified113Residue m A [MOD 8 * m])
    (hp3 : p ≡ 1 [MOD 3]) :
    @legendreSym p ⟨hp⟩ (-(3 * (m : ℤ))) = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let n := m / 2
  have hmn : m = 2 * n := by dsimp [n]; omega
  have hnodd : Odd n := by
    apply Nat.odd_iff.mpr
    rcases hrow with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, hα⟩ <;> omega
  have hp8 : p % 8 = α % 8 :=
    (hpr.of_dvd (dvd_mul_right 8 m)).trans
      (unramified113_residue_mod_eight hm hrow)
  have hp4 : p % 4 = 1 := by
    rcases hrow with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, rfl⟩ <;> norm_num at hp8 <;> omega
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hA : A = 1 ∨ A = 3 := by
    rcases hrow with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, hα⟩ <;> omega
  have hnA : n.Coprime A := by
    rcases hA with rfl | rfl
    · simp
    · rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
      intro hd
      exact h3 (dvd_trans hd (by rw [hmn]; exact dvd_mul_left n 2))
  have hsquare : jacobiSym ((A : ℤ) ^ 2) n = 1 := by
    apply jacobiSym.sq_one'
    simpa only [Int.gcd_natCast_natCast] using hnA.symm
  have hpn : p ≡ unramified113Residue m A [MOD n] :=
    hpr.of_dvd (by rw [hmn]; exact ⟨16, by ring⟩)
  have hid : A ^ 2 + unramified113Residue m A =
      n * (2 * (8 * A ^ 2 + 5)) := by
    rw [unramified113_residue_identity hm hrow, hmn]
    ring
  have hswap : jacobiSym (n : ℤ) p = ZMod.χ₄ n := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hnodd hp4,
      jacobi_of_separator_residue hpn hid, Nat.cast_pow,
      jacobiSym.neg _ hnodd, hsquare, mul_one]
  have hsign : ZMod.χ₈ p * ZMod.χ₄ n = 1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four]
    rcases hrow with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, rfl⟩ <;> norm_num at hp8 <;>
      split_ifs <;> omega
  rw [jacobiSym.legendreSym.to_jacobiSym,
    show -(3 * (m : ℤ)) = (-3) * (2 * (n : ℤ)) by
      rw [hmn]; push_cast; ring,
    jacobiSym.mul_left, jacobi_neg_three_eq_one hpodd
      (by simpa [Nat.ModEq] using hp3),
    one_mul, jacobiSym.mul_left, jacobiSym.at_two hpodd, hswap]
  exact hsign

/-- `Ramified113Reciprocity` for even `m₁` (the two even rows). -/
theorem ramified113_reciprocity_of_even {m₁ A₀ α p : ℕ}
    (hm₁ : 0 < m₁) (heven : m₁ % 2 = 0) (h3 : m₁ % 3 = 1)
    (hrow : IsRamified113Row m₁ A₀ α) (hp : p.Prime)
    (hpr : p ≡ ramified113Residue m₁ A₀ [MOD 8 * m₁]) :
    @legendreSym p ⟨hp⟩ (-(m₁ : ℤ)) = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let n := m₁ / 2
  have hmn : m₁ = 2 * n := by dsimp [n]; omega
  have hnodd : Odd n := by
    apply Nat.odd_iff.mpr
    rcases hrow with h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, hα⟩ <;> omega
  have hn3 : n % 3 = 2 := by omega
  have hA : A₀ = 1 := by
    rcases hrow with h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, hα⟩ <;> omega
  have hp8 : p % 8 = α % 8 :=
    (hpr.of_dvd (dvd_mul_right 8 m₁)).trans
      (ramified113_residue_mod_eight hm₁ hrow)
  have hp4 : p % 4 = 3 := by
    rcases hrow with h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, rfl⟩ <;> norm_num at hp8 <;> omega
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hpn : p ≡ ramified113Residue m₁ A₀ [MOD n] :=
    hpr.of_dvd (by rw [hmn]; exact ⟨16, by ring⟩)
  have hid : 3 + ramified113Residue m₁ A₀ = n * 26 := by
    have hi := ramified113_residue_identity hm₁ hrow
    rw [hA, hmn] at hi
    norm_num at hi
    calc
      3 + ramified113Residue m₁ A₀ =
          3 + ramified113Residue (2 * n) 1 := by rw [hmn, hA]
      _ = 2 * n * 13 := hi
      _ = n * 26 := by omega
  have hpn_symbol : jacobiSym (p : ℤ) n = -1 := by
    rw [jacobi_of_separator_residue hpn hid]
    norm_num only [Nat.cast_ofNat]
    rw [jacobi_neg_three_swap hnodd, jacobiSym.mod_left]
    have hn3z : (n : ℤ) % 3 = 2 := by exact_mod_cast hn3
    exact (congrArg (fun z : ℤ => jacobiSym z 3) hn3z).trans (by norm_num)
  have hswap : jacobiSym (n : ℤ) p = -(ZMod.χ₄ n) := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hnodd) with hn4 | hn4
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four hn4 hpodd,
        hpn_symbol, ZMod.χ₄_nat_one_mod_four hn4]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four hn4 hp4,
        hpn_symbol, ZMod.χ₄_nat_three_mod_four hn4]
  have hsign : ZMod.χ₈' p * -(ZMod.χ₄ n) = 1 := by
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four]
    rcases hrow with h | h | h | h | h | h <;>
      rcases h with ⟨hr, ha, rfl⟩ <;> norm_num at hp8 <;>
      split_ifs <;> omega
  rw [jacobiSym.legendreSym.to_jacobiSym,
    show -(m₁ : ℤ) = (-2) * (n : ℤ) by
      rw [hmn]; push_cast; ring,
    jacobiSym.mul_left, jacobiSym.at_neg_two hpodd, hswap]
  exact hsign

/-- The reciprocity condition of the unramified case holds. -/
theorem unramified113Reciprocity : Unramified113Reciprocity := by
  intro m A α p hm h3 hrow hp hpr hp3
  by_cases heven : m % 2 = 0
  · exact unramified113_reciprocity_of_even hm heven h3 hrow hp hpr hp3
  · exact unramified113_reciprocity_of_odd hm
      (Nat.odd_iff.mpr (by omega)) h3 hrow hp hpr hp3

/-- The reciprocity condition of the ramified case holds. -/
theorem ramified113Reciprocity : Ramified113Reciprocity := by
  intro m A α p hm h3 hrow hp hpr
  by_cases heven : m % 2 = 0
  · exact ramified113_reciprocity_of_even hm heven h3 hrow hp hpr
  · exact ramified113_reciprocity_of_odd hm
      (Nat.odd_iff.mpr (by omega)) h3 hrow hp hpr

/-- The integer data of the Mordell construction for `⟨1,1,3⟩` exist for every
input of `Mordell113Witnesses`. -/
theorem mordell113Witnesses : Mordell113Witnesses :=
  mordell113Witnesses_of_reciprocity
    unramified113Reciprocity ramified113Reciprocity

/-- The classification of positive ternaries of determinant 3 implies
`Regular113Sufficiency`. `ClassicalInputs.Regular113.Classification` proves the classification. -/
theorem regular113Sufficiency_of_classification
    (hclass : DeterminantThreeClassification) :
    Regular113.Regular113Sufficiency :=
  regular113Sufficiency_of_witnesses mordell113Witnesses hclass

end FibonacciCriterion.MordellRegularity

