import FibonacciCriterion.Forms.QuaternaryExtension
import FibonacciCriterion.Arithmetic.QuadraticCongruence
import FibonacciCriterion.ClassicalInputs.Representation
import FibonacciCriterion.Arithmetic.PrimePowerNormalization

/-!
# Tools for obstructions at odd primes (Lemmas 5.8 and 5.10)

For `(p, α) = (3, 1)` or `(5, 2)`, the escalator `⟨1, α, p⟩` is `⟨1,1,3⟩` or
`⟨1,2,5⟩`. By Proposition 3.2 it represents a nonnegative integer unless the
`p`-adic valuation is odd and the unit part is a nonsquare modulo `p`
(`represents_iff`, from the fields `regular113_criterion` and
`regular125_criterion` of `ClassicalInputs`).

This file proves, for both primes at once:

* Lemma 5.8: `x² + α y² + p z² + 2 a z` represents every nonnegative integer
  when `p ∤ a` (`represents_phi`);
* Lemma 5.10: `⟨1, α, p⟩ ⊥ ⟨p b⟩` represents `p^a u` when `a` is odd,
  `p ∤ u`, `u` is a nonsquare modulo `p`, `b > 0`, `p ∤ b`, and `u > 4 b`
  (`exists_sub_represents`); for `p = 5` the choice of `t` comes from
  Lemma 5.9;
* Lemma 3.6 for these escalators in integral form: `⟨1, α, p⟩` omits every
  nonzero square multiple of an obstructed integer (`not_represents_sq_mul`).
-/

namespace FibonacciCriterion

namespace OddPrime

open ClassicalRepresentation TernaryGram

/-- The parameters `(p, α) = (3, 1)` and `(5, 2)` of the escalators `⟨1, α, p⟩`
with obstructions at odd primes. -/
def IsData (p α : ℤ) : Prop := (p = 3 ∧ α = 1) ∨ (p = 5 ∧ α = 2)

/-- `u` is a square modulo `p`. -/
def IsSquareMod (p u : ℤ) : Prop := ∃ y : ℤ, p ∣ u - y ^ 2

/-- The local obstruction of Proposition 3.2 at `p`: odd valuation and
nonsquare unit part. -/
def Obstructed (p N : ℤ) : Prop :=
  ∃ (e : ℕ) (u : ℤ), N = p ^ e * u ∧ ¬ p ∣ u ∧ Odd e ∧ ¬ IsSquareMod p u

theorem isSquareMod_three (u : ℤ) : IsSquareMod 3 u ↔ u % 3 ≠ 2 := by
  constructor
  · rintro ⟨y, hy⟩
    have : y ^ 2 % 3 = 0 ∨ y ^ 2 % 3 = 1 := by
      rcases (by omega : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2) with h | h | h <;>
        simp [pow_two, Int.mul_emod, h]
    omega
  · intro h
    rcases (by omega : u % 3 = 0 ∨ u % 3 = 1) with h0 | h1
    · exact ⟨0, by omega⟩
    · exact ⟨1, by omega⟩

theorem isSquareMod_five (u : ℤ) :
    IsSquareMod 5 u ↔ u % 5 ≠ 2 ∧ u % 5 ≠ 3 := by
  constructor
  · rintro ⟨y, hy⟩
    have : y ^ 2 % 5 = 0 ∨ y ^ 2 % 5 = 1 ∨ y ^ 2 % 5 = 4 := by
      rcases (by omega : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨
          y % 5 = 4) with h | h | h | h | h <;>
        simp [pow_two, Int.mul_emod, h]
    omega
  · intro h
    rcases (by omega : u % 5 = 0 ∨ u % 5 = 1 ∨ u % 5 = 4) with h0 | h1 | h4
    · exact ⟨0, by omega⟩
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩

theorem not_dvd_iff_emod {p u : ℤ} : ¬ p ∣ u ↔ u % p ≠ 0 :=
  not_congr Int.dvd_iff_emod_eq_zero

/-- The factorization `N = p^e u` with `p ∤ u` is unique. -/
theorem normalization_unique {p : ℤ} (hp : 2 ≤ p) {e e' : ℕ} {u u' : ℤ}
    (hu : ¬ p ∣ u) (hu' : ¬ p ∣ u') (h : p ^ e * u = p ^ e' * u') :
    e = e' ∧ u = u' := by
  have he := pow_mul_unit_exponent_unique p hp (not_dvd_iff_emod.1 hu)
    (not_dvd_iff_emod.1 hu') h
  subst he
  exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero _ (by omega)) h⟩

/-- An integer with even valuation or square unit part is not obstructed. -/
theorem not_obstructed {p : ℤ} (hp : 2 ≤ p) (e : ℕ) (u : ℤ) (hu : ¬ p ∣ u)
    (hloc : Even e ∨ IsSquareMod p u) : ¬ Obstructed p (p ^ e * u) := by
  rintro ⟨e', u', h, hu', ho, hns⟩
  obtain ⟨rfl, rfl⟩ := normalization_unique hp hu hu' h
  rcases hloc with he | hs
  · exact (Nat.not_odd_iff_even.2 he) ho
  · exact hns hs

/-- `(diag 1 1 3).Represents` is `Represents113`. -/
theorem represents_113_iff (n : ℤ) :
    (diag 1 1 3).Represents n ↔ Represents113 n := by
  simp [TernaryGram.Represents, Represents113]

/-- `(diag 1 2 5).Represents` is `Represents125`. -/
theorem represents_125_iff (n : ℤ) :
    (diag 1 2 5).Represents n ↔ Represents125 n := by
  simp [TernaryGram.Represents, Represents125]

/-- `n = 9^a (9b + 6)` exactly when `n` is obstructed at 3. -/
theorem exceptional113_iff (n : ℤ) : Exceptional113 n ↔ Obstructed 3 n := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨2 * a + 1, 3 * b + 2, ?_, by omega, ⟨a, rfl⟩,
      (isSquareMod_three _).not.2 (by omega)⟩
    rw [pow_succ, pow_mul]
    ring
  · rintro ⟨e, u, rfl, hu, ⟨a, rfl⟩, hns⟩
    rw [isSquareMod_three, not_not] at hns
    obtain ⟨b, hb⟩ : ∃ b, u = 3 * b + 2 := ⟨u / 3, by omega⟩
    refine ⟨a, b, ?_⟩
    rw [hb, pow_succ, pow_mul]
    norm_num
    ring

/-- `n = 5 · 25^a (5b + r)` with `r ∈ {2, 3}` exactly when `n` is obstructed
at 5. -/
theorem exceptional125_iff (n : ℤ) : Exceptional125 n ↔ Obstructed 5 n := by
  constructor
  · rintro ⟨a, b, r, hr, rfl⟩
    refine ⟨2 * a + 1, 5 * b + r, ?_, by omega, ⟨a, rfl⟩,
      (isSquareMod_five _).not.2 (by omega)⟩
    rw [pow_succ, pow_mul]
    ring
  · rintro ⟨e, u, rfl, hu, ⟨a, rfl⟩, hns⟩
    rw [isSquareMod_five, not_and_or, not_not, not_not] at hns
    obtain ⟨b, r, hr, hb⟩ : ∃ b r, (r = 2 ∨ r = 3) ∧ u = 5 * b + r :=
      ⟨u / 5, u % 5, by omega, by omega⟩
    refine ⟨a, b, r, hr, ?_⟩
    rw [hb, pow_succ, pow_mul, show (5 : ℤ) ^ 2 = 25 by norm_num]
    ring

/-- Proposition 3.2 for `⟨1,1,3⟩` and `⟨1,2,5⟩`: a nonnegative integer is
represented exactly when it is not obstructed at `p`. -/
theorem represents_iff (i : ClassicalInputs) {p α : ℤ} (h : IsData p α) {N : ℤ} (hN : 0 ≤ N) :
    (diag 1 α p).Represents N ↔ ¬ Obstructed p N := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [represents_113_iff, ← exceptional113_iff]
    exact i.regular113_criterion N hN
  · rw [represents_125_iff, ← exceptional125_iff]
    exact i.regular125_criterion N hN

theorem two_le {p α : ℤ} (h : IsData p α) : 2 ≤ p := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num

theorem prime {p α : ℤ} (h : IsData p α) : Prime p := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Int.prime_three
  · exact Int.prime_iff_natAbs_prime.2 (by norm_num)

/-- Proposition 3.2 in valuation form: `⟨1, α, p⟩` represents `p^e u` when
`u ≥ 0`, `p ∤ u`, and either `e` is even or `u` is a square modulo `p`. -/
theorem represents_of_local (i : ClassicalInputs) {p α : ℤ} (h : IsData p α) (e : ℕ) (u : ℤ)
    (hu0 : 0 ≤ u) (hu : ¬ p ∣ u) (hloc : Even e ∨ IsSquareMod p u) :
    (diag 1 α p).Represents (p ^ e * u) := by
  have hp := two_le h
  exact (represents_iff i h (by positivity)).2 (not_obstructed hp e u hu hloc)

/-- Proposition 3.2 in valuation form: `⟨1, α, p⟩` omits `p^e u` when `p ∤ u`,
`e` is odd, and `u` is a nonsquare modulo `p`. -/
theorem not_represents_of_local (i : ClassicalInputs) {p α : ℤ} (h : IsData p α) (e : ℕ) (u : ℤ)
    (hu : ¬ p ∣ u) (ho : Odd e) (hns : ¬ IsSquareMod p u) :
    ¬ (diag 1 α p).Represents (p ^ e * u) := by
  intro hrep
  have hu0 : 0 ≤ p ^ e * u := by
    obtain ⟨x, y, z, hxyz⟩ := hrep
    rw [← hxyz, diag_eval]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> positivity
  exact (represents_iff i h hu0).1 hrep ⟨e, u, rfl, hu, ho, hns⟩

/-- If `x² + α y²` vanishes modulo `p`, both coordinates vanish: the cases
`RegularReductions.dvd_three_of_sq_add_sq` and
`RegularReductions.dvd_five_of_sq_add_two_sq`. -/
theorem dvd_of_dvd_sq_add {p α : ℤ} (h : IsData p α) (X Y : ℤ)
    (hd : p ∣ X ^ 2 + α * Y ^ 2) : p ∣ X ∧ p ∣ Y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [one_mul] at hd
    obtain ⟨hX, hY⟩ := RegularReductions.dvd_three_of_sq_add_sq X Y
      (Int.emod_eq_zero_of_dvd hd)
    exact ⟨Int.dvd_of_emod_eq_zero hX, Int.dvd_of_emod_eq_zero hY⟩
  · obtain ⟨hX, hY⟩ := RegularReductions.dvd_five_of_sq_add_two_sq X Y
      (Int.emod_eq_zero_of_dvd hd)
    exact ⟨Int.dvd_of_emod_eq_zero hX, Int.dvd_of_emod_eq_zero hY⟩

/-- Lemma 5.8: for `(p, α) = (3, 1)` or `(5, 2)` and `p ∤ a`, the polynomial
`Φ_{p,a}(x, y, z) = x² + α y² + p z² + 2 a z` represents every nonnegative
integer. -/
theorem represents_phi (i : ClassicalInputs) {p α : ℤ} (h : IsData p α) (a : ℤ) (ha : ¬ p ∣ a)
    (r : ℤ) (hr : 0 ≤ r) :
    ∃ x y z : ℤ, x ^ 2 + α * y ^ 2 + p * z ^ 2 + 2 * a * z = r := by
  have hp := two_le h
  have hpr := prime h
  -- `p² r + p a²` has valuation 1 and square unit part.
  have hunit : ¬ p ∣ p * r + a ^ 2 := by
    intro hd
    have : p ∣ a ^ 2 := (dvd_add_right (dvd_mul_right p r)).1 hd
    exact ha (hpr.dvd_of_dvd_pow this)
  obtain ⟨X, Y, Z, hXYZ⟩ := represents_of_local i h 1 (p * r + a ^ 2)
    (by nlinarith [sq_nonneg a]) hunit (Or.inr ⟨a, by simp⟩)
  rw [diag_eval] at hXYZ
  -- `p ∣ X, Y`.
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := dvd_of_dvd_sq_add h X Y
    ⟨r * p + a ^ 2 - Z ^ 2, by linear_combination hXYZ⟩
  have hbase : p * x ^ 2 + α * p * y ^ 2 + Z ^ 2 = p * r + a ^ 2 := by
    apply mul_left_cancel₀ (show p ≠ 0 by omega)
    linear_combination hXYZ
  -- `Z ≡ ± a (mod p)`.
  have hZ : p ∣ (Z - a) * (Z + a) :=
    ⟨r - x ^ 2 - α * y ^ 2, by linear_combination hbase⟩
  rcases hpr.dvd_or_dvd hZ with ⟨z, hz⟩ | ⟨z, hz⟩
  · refine ⟨x, y, z, ?_⟩
    apply mul_left_cancel₀ (show p ≠ 0 by omega)
    have hZ' : Z = p * z + a := by linarith
    subst hZ'
    linear_combination hbase
  · refine ⟨x, y, -z, ?_⟩
    apply mul_left_cancel₀ (show p ≠ 0 by omega)
    have hZ' : Z = p * z - a := by linarith
    subst hZ'
    linear_combination hbase

theorem pow_odd_eq {p : ℤ} (j : ℕ) : p ^ (2 * j + 1) = p * (p ^ j) ^ 2 := by
  rw [← pow_mul, mul_comm j 2, pow_succ]
  ring

theorem sq_zmod_five (x : ZMod 5) (hx : x ≠ 0) : x ^ 2 = 1 ∨ x ^ 2 = 4 := by
  revert x
  decide

/-- Lemma 5.10: let `N = p^a u` with `a` odd, `p ∤ u`, and `u` a nonsquare
modulo `p`, and let `q = p b` with `p ∤ b`, `b > 0`, and `u > 4 b`. Then
`⟨1, α, p⟩ ⊥ ⟨q⟩` represents `N`: some `N - q k²` is represented by the
escalator. -/
theorem exists_sub_represents (i : ClassicalInputs) {p α : ℤ} (h : IsData p α) {N q : ℤ} (a : ℕ)
    (u b : ℤ) (ha : Odd a) (hN : N = p ^ a * u) (hu : ¬ p ∣ u)
    (hns : ¬ IsSquareMod p u) (hq : q = p * b) (hb : ¬ p ∣ b) (hb0 : 0 < b)
    (hub : 4 * b < u) :
    ∃ k : ℤ, (diag 1 α p).Represents (N - q * k ^ 2) := by
  obtain ⟨j, rfl⟩ := ha
  -- With `k = p^j t`, the difference is `p^a (u - b t²)`.
  have hdiff : ∀ t : ℤ, N - q * (p ^ j * t) ^ 2 = p ^ (2 * j + 1) * (u - b * t ^ 2) := by
    intro t
    rw [hN, hq, pow_odd_eq]
    ring
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `p = 3`: here `u ≡ 2 (mod 3)`.
    rw [isSquareMod_three, not_not] at hns
    rw [not_dvd_iff_emod] at hb
    rcases (by omega : b % 3 = 1 ∨ b % 3 = 2) with hb1 | hb2
    · refine ⟨3 ^ j * 1, ?_⟩
      rw [hdiff]
      exact represents_of_local i (Or.inl ⟨rfl, rfl⟩) _ _ (by nlinarith)
        (by rw [not_dvd_iff_emod]; omega)
        (Or.inr ((isSquareMod_three _).2 (by omega)))
    · -- Both `u - b` and `u - 4 b` are divisible by 3; one has valuation 1.
      have h9 : ¬ (9 ∣ u - b * 1 ^ 2 ∧ 9 ∣ u - b * 2 ^ 2) := by
        rintro ⟨h1, h2⟩
        have := dvd_sub h1 h2
        omega
      obtain ⟨t, ht, h9t⟩ : ∃ t : ℤ, (t = 1 ∨ t = 2) ∧ ¬ 9 ∣ u - b * t ^ 2 := by
        by_cases h1 : 9 ∣ u - b * 1 ^ 2
        · exact ⟨2, Or.inr rfl, fun h2 => h9 ⟨h1, h2⟩⟩
        · exact ⟨1, Or.inl rfl, h1⟩
      have h3 : 3 ∣ u - b * t ^ 2 := by
        rcases ht with rfl | rfl <;> omega
      obtain ⟨w, hw⟩ := h3
      refine ⟨3 ^ j * t, ?_⟩
      rw [hdiff, hw, show (3 : ℤ) ^ (2 * j + 1) * (3 * w) = 3 ^ (2 * j + 2) * w by ring]
      have hpos : 0 < u - b * t ^ 2 := by rcases ht with rfl | rfl <;> nlinarith
      refine represents_of_local i (Or.inl ⟨rfl, rfl⟩) _ _ (by omega) ?_
        (Or.inl ⟨j + 1, by ring⟩)
      rintro ⟨w', rfl⟩
      exact h9t ⟨w', by rw [hw]; ring⟩
  · -- `p = 5`: Lemma 5.9 supplies `t`.
    have hu5 : ((u : ℤ) : ZMod 5) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hu
    have hb5 : ((b : ℤ) : ZMod 5) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hb
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨t, htle, ⟨x, hx0, hx⟩, ht0⟩ :=
      exists_sub_mul_sq_square 5 le_rfl u b hu5 hb5
    have hnsZ : ∀ y : ZMod 5, y ^ 2 ≠ (u : ZMod 5) := by
      intro y hy
      apply hns
      refine ⟨(y.val : ℤ), ?_⟩
      have hy' : (((y.val : ℤ) ^ 2 : ℤ) : ZMod 5) = (u : ZMod 5) := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        exact hy
      exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 5).1 hy'
    have ht : t ^ 2 = 1 ∨ t ^ 2 = 4 := by
      have := ht0 hnsZ
      have h2 : t.natAbs ≤ 2 := by simpa using htle
      rcases (by omega : t.natAbs = 1 ∨ t.natAbs = 2) with h | h
      · left
        rw [← Int.natAbs_sq, h]
        norm_num
      · right
        rw [← Int.natAbs_sq, h]
        norm_num
    have hw : (u - b * t ^ 2) % 5 = 1 ∨ (u - b * t ^ 2) % 5 = 4 := by
      rcases sq_zmod_five x hx0 with h1 | h4
      · left
        rw [h1] at hx
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (u - b * t ^ 2) 5).1
          (by exact_mod_cast hx)
        omega
      · right
        rw [h4] at hx
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub 4 (u - b * t ^ 2) 5).1
          (by exact_mod_cast hx)
        omega
    refine ⟨5 ^ j * t, ?_⟩
    rw [hdiff]
    exact represents_of_local i (Or.inr ⟨rfl, rfl⟩) _ _
      (by rcases ht with h | h <;> rw [h] <;> nlinarith)
      (by rw [not_dvd_iff_emod]; omega)
      (Or.inr ((isSquareMod_five _).2 (by omega)))

/-- Lemma 3.6 for `⟨1,1,3⟩` and `⟨1,2,5⟩` in integral form: `⟨1, α, p⟩` omits
every nonzero square multiple of an obstructed integer `p^e u`. -/
theorem not_represents_sq_mul (i : ClassicalInputs) {p α : ℤ} (h : IsData p α) (e : ℕ) (u : ℤ)
    (hu : ¬ p ∣ u) (ho : Odd e) (hns : ¬ IsSquareMod p u) (k : ℤ) (hk : k ≠ 0) :
    ¬ (diag 1 α p).Represents (k ^ 2 * (p ^ e * u)) := by
  have hp := two_le h
  have hpp : ((p.toNat : ℕ) : ℤ) = p := Int.toNat_of_nonneg (by omega)
  obtain ⟨s, ω, hk', hω⟩ := exists_pow_mul_not_dvd p.toNat (by omega) k hk
  rw [hpp] at hk' hω
  subst hk'
  have hfac : (p ^ s * ω) ^ 2 * (p ^ e * u) = p ^ (2 * s + e) * (ω ^ 2 * u) := by
    rw [pow_add, pow_mul]
    ring
  rw [hfac]
  apply not_represents_of_local i h
  · intro hd
    rcases (prime h).dvd_or_dvd hd with h1 | h1
    · exact hω ((prime h).dvd_of_dvd_pow h1)
    · exact hu h1
  · rcases ho with ⟨j, rfl⟩
    exact ⟨s + j, by ring⟩
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [isSquareMod_three, not_not] at hns ⊢
      rw [not_dvd_iff_emod] at hω
      have : ω ^ 2 % 3 = 1 := by
        rcases (by omega : ω % 3 = 1 ∨ ω % 3 = 2) with h | h <;>
          simp [pow_two, Int.mul_emod, h]
      rw [Int.mul_emod, this, hns]
      norm_num
    · rw [isSquareMod_five, not_and_or, not_not, not_not] at hns ⊢
      rw [not_dvd_iff_emod] at hω
      have : ω ^ 2 % 5 = 1 ∨ ω ^ 2 % 5 = 4 := by
        rcases (by omega : ω % 5 = 1 ∨ ω % 5 = 2 ∨ ω % 5 = 3 ∨ ω % 5 = 4) with
          h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
      rcases this with h1 | h1 <;> rcases hns with h2 | h2 <;>
        simp [Int.mul_emod, h1, h2]

end OddPrime

end FibonacciCriterion
