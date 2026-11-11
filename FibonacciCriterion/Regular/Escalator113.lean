import FibonacciCriterion.Regular.OddPrimeTools
import FibonacciCriterion.Forms.QuaternaryExtension
import FibonacciCriterion.Fibonacci.Growth
import FibonacciCriterion.ClassicalInputs.Definitions

/-!
# Fibonacci-universality of extensions of `⟨1,1,3⟩` (Proposition 5.11)

`⟨1,1,3⟩` omits a positive integer exactly when its 3-adic valuation is odd
and its unit part is `2 (mod 3)`. Its Fibonacci truant is `F₁₆ = 987`. The
proof follows §5.3 of the manuscript.

* `not_represents_sq_mul_truant`: Lemma 3.6 for `⟨1,1,3⟩`.
* `exists_rep`: the representatives `c = (0, 0, c₃)`, `c₃ ∈ {0, 1, 2}` of §4.1.
* `not_nine_dvd_q`: Lemma 4.3 for `⟨1,1,3⟩`, `v₃(q) ≤ 1`.
* `obstructed_index`: a Fibonacci member of the exceptional set has index 16,
  20, or at least 28.
* `exception_data`: every later Fibonacci exception is at least `F₂₀`, with
  unit part `u > 4 · 329` (from `F₂₀ = 3 · 2255` and, for `n ≥ 28`, from the
  bound (1) and Lemma 2.1 with the cutoff `F₂₈ / 84`).
* `fibonacciUniversal`: Proposition 5.11.
* `represents_fib_below_sixteen`: `⟨1,1,3⟩` represents `Fₙ` for `n < 16` (the
  truant column of Figure 1), used in `Escalation.TernaryTruants`.
-/

namespace FibonacciCriterion

namespace Escalator113

open OddPrime TernaryGram QuaternaryExtension

/-- The escalator `⟨1,1,3⟩`. -/
abbrev T : TernaryGram := diag 1 1 3

theorem data : IsData 3 1 := Or.inl ⟨rfl, rfl⟩

theorem det_pos : 0 < T.det := by norm_num

theorem posDef : T.PosDef := diag_posDef (by norm_num) (by norm_num) (by norm_num)

/-- The unit part 329 of the truant `987 = 3 · 329` is a nonsquare modulo 3
(Lemma 2.4). -/
theorem truant_not_square : ¬ IsSquareMod 3 329 := by
  rw [isSquareMod_three]
  norm_num

/-- Lemma 3.6 for `⟨1,1,3⟩`: it omits every nonzero square multiple of its
truant `987 = 3 · 329`. -/
theorem not_represents_sq_mul_truant (i : ClassicalInputs) (k : ℤ) (hk : k ≠ 0) :
    ¬ T.Represents (k ^ 2 * 987) := by
  have := not_represents_sq_mul i data 1 329 (by norm_num) odd_one
    truant_not_square k hk
  simpa using this

/-- Lemma 3.6 with `k = 1`: `⟨1,1,3⟩` omits its truant 987. -/
theorem not_represents_truant (i : ClassicalInputs) : ¬ T.Represents 987 := by
  simpa using not_represents_sq_mul_truant i 1 one_ne_zero

/-- The representatives of §4.1 for `⟨1,1,3⟩`: after a change of generator,
`c = (0, 0, c₃)` with `0 ≤ c₃ ≤ 2`. -/
theorem exists_rep (M : QuaternaryExtension T) :
    ∃ a₁ a₂ a₃ : ℤ, (M.shift a₁ a₂ a₃).c₁ = 0 ∧ (M.shift a₁ a₂ a₃).c₂ = 0 ∧
      0 ≤ (M.shift a₁ a₂ a₃).c₃ ∧ (M.shift a₁ a₂ a₃).c₃ < 3 := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h2', h3, h3'⟩ :=
    exists_shift_diag (B := 1) (C := 3) (by norm_num) (by norm_num) 0 0 M
  exact ⟨a₁, a₂, a₃, h1, by omega, by omega, by omega⟩

/-- The value of `q` for the representative `c = (0, 0, c₃)`: `q = m` if
`c₃ = 0`, and `q = 9 m - 3 c₃²` (with `d = 3`) otherwise. -/
theorem q_rep (c₃ m : ℤ) (hc : 0 ≤ c₃ ∧ c₃ < 3) :
    (⟨0, 0, c₃, m⟩ : QuaternaryExtension T).q =
      if c₃ = 0 then m else 9 * m - 3 * c₃ ^ 2 := by
  rcases (by omega : c₃ = 0 ∨ c₃ = 1 ∨ c₃ = 2) with rfl | rfl | rfl <;>
    quaternary_norm <;> ring

/-- Lemma 4.3 for `⟨1,1,3⟩`: an extension representing 987 has
`v₃(q) ≤ 1`. -/
theorem not_nine_dvd_q (i : ClassicalInputs) (M : QuaternaryExtension T)
    (h987 : M.Represents 987) : ¬ 9 ∣ M.q := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h3, h3'⟩ := exists_rep M
  rw [← q_shift det_pos M a₁ a₂ a₃]
  have h987' := (represents_shift_iff M a₁ a₂ a₃).2 h987
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h3 h3' h987'
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h3 h3'
  subst h1 h2
  rw [q_rep c₃ m ⟨h3, h3'⟩]
  split_ifs with hc
  · -- `c₃ = 0`, so `d = 1` and `M = T ⊥ ⟨m⟩`.
    subst hc
    rintro ⟨s, rfl⟩
    obtain ⟨x, y, z, w, hxyzw⟩ := h987'
    have hrep : T.Represents (3 ^ 1 * (329 - 3 * (s * w ^ 2))) := by
      refine ⟨x, y, z, ?_⟩
      simp only [QuaternaryExtension.eval, diag_eval] at hxyzw ⊢
      linear_combination hxyzw
    generalize s * w ^ 2 = t at hrep
    exact not_represents_of_local i data 1 (329 - 3 * t) (by omega) odd_one
      ((isSquareMod_three _).not.2 (by omega)) hrep
  · -- `c₃ ≠ 0`, so `q = 9 m - 3 c₃²` has valuation 1.
    rcases (by omega : c₃ = 1 ∨ c₃ = 2) with rfl | rfl <;> omega

/-- A Fibonacci member of the exceptional set of `⟨1,1,3⟩` has index 16, 20,
or at least 28 (Lemma 2.4 and the proof of Proposition 5.11): its index is
divisible by 4, and `F₄`, `F₈`, `F₁₂`, `F₂₄` are not members. -/
theorem obstructed_index (n a : ℕ) (u : ℤ) (hfac : (Nat.fib n : ℤ) = 3 ^ a * u)
    (hu : ¬ 3 ∣ u) (ho : Odd a) (hns : ¬ IsSquareMod 3 u) :
    n = 16 ∨ n = 20 ∨ 28 ≤ n := by
  -- `3 ∣ Fₙ`, hence `4 ∣ n`.
  have h3 : 3 ∣ Nat.fib n := by
    have : (3 : ℤ) ∣ Nat.fib n := by
      rw [hfac]
      obtain ⟨j, rfl⟩ := ho
      exact (dvd_pow_self 3 (by omega)).mul_right u
    exact_mod_cast this
  have h4 : 4 ∣ n := (three_dvd_fib_iff n).1 h3
  -- A factorization `Fₙ = 3^e v` with `3 ∤ v` determines `(a, u)`.
  have pin : ∀ (e : ℕ) (v : ℤ), ¬ 3 ∣ v → (Nat.fib n : ℤ) = 3 ^ e * v →
      e = a ∧ v = u := fun e v hv he =>
    normalization_unique (by norm_num) hv hu (he.symm.trans hfac)
  obtain ⟨j, rfl⟩ := h4
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨
    7 ≤ j) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hj
  · simp at hfac
    exact absurd (hfac ▸ dvd_zero 3) hu
  · obtain ⟨-, rfl⟩ := pin 1 1 (by norm_num) (by decide)
    exact absurd ((isSquareMod_three _).2 (by norm_num)) hns
  · obtain ⟨-, rfl⟩ := pin 1 7 (by norm_num) (by decide)
    exact absurd ((isSquareMod_three _).2 (by norm_num)) hns
  · obtain ⟨rfl, -⟩ := pin 2 16 (by norm_num) (by decide)
    exact absurd ho (by decide)
  · left; rfl
  · right; left; rfl
  · obtain ⟨rfl, -⟩ := pin 2 5152 (by norm_num) (by decide)
    exact absurd ho (by decide)
  · right; right; omega

/-- Proposition 3.2 for `⟨1,1,3⟩`, truant column: `⟨1,1,3⟩` represents `Fₙ`
for every `n < 16`, by Lemma 2.4. -/
theorem represents_fib_below_sixteen (i : ClassicalInputs) (n : ℕ) (hn : n < 16) :
    T.Represents (Nat.fib n) := by
  by_contra hT
  have hob := (not_congr (represents_iff i data
    (show (0 : ℤ) ≤ Nat.fib n by positivity))).1 hT
  rw [not_not] at hob
  obtain ⟨a, u, hfac, hu, ho, hns⟩ := hob
  rcases obstructed_index n a u hfac hu ho hns with h | h | h <;> omega

/-- Every Fibonacci exception `Fₙ ≠ 987` of `⟨1,1,3⟩` is at least
`F₂₀ = 6765` and has the form `3^a u` with `a` odd, `u ≡ 2 (mod 3)`, and
`u > 4 · 329`. Its index is divisible by 4. At `F₂₀ = 3 · 2255` the bound on
`u` is direct; otherwise the index is at least 28 (`F₂₄` has even valuation),
and the bound `3^{v₃(Fₙ)} ≤ 3n` with Lemma 2.1 gives
`u ≥ Fₙ / (3n) ≥ F₂₈ / 84`. -/
theorem exception_data (i : FibonacciClassicalInputs) (n : ℕ)
    (hn : ¬ T.Represents (Nat.fib n)) (h987 : Nat.fib n ≠ 987) :
    6765 ≤ Nat.fib n ∧ ∃ (a : ℕ) (u : ℤ), (Nat.fib n : ℤ) = 3 ^ a * u ∧
      Odd a ∧ ¬ 3 ∣ u ∧ ¬ IsSquareMod 3 u ∧ 4 * 329 < u := by
  have hob := (not_congr (represents_iff i.representation data
    (show (0 : ℤ) ≤ Nat.fib n by positivity))).1 hn
  rw [not_not] at hob
  obtain ⟨a, u, hfac, hu, ho, hns⟩ := hob
  have pin : ∀ (e : ℕ) (v : ℤ), ¬ 3 ∣ v → (Nat.fib n : ℤ) = 3 ^ e * v →
      e = a ∧ v = u := fun e v hv he =>
    normalization_unique (by norm_num) hv hu (he.symm.trans hfac)
  have hsmall : n = 20 ∨ 28 ≤ n := by
    rcases obstructed_index n a u hfac hu ho hns with rfl | h | h
    · exact absurd (by decide) h987
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨?_, a, u, hfac, ho, hu, hns, ?_⟩
  · rcases hsmall with rfl | h
    · decide
    · calc 6765 ≤ Nat.fib 28 := by decide
        _ ≤ Nat.fib n := Nat.fib_mono h
  · rcases hsmall with rfl | h28
    · obtain ⟨-, rfl⟩ := pin 1 2255 (by norm_num) (by decide)
      norm_num
    · -- Bound (1) and Lemma 2.1.
      obtain ⟨a', u', hfac', hu', hbound⟩ :=
        FibonacciValuationInputs.three_prime_power_bound i.valuations n (by omega)
      obtain ⟨rfl, rfl⟩ := pin a' u'
        (fun h => hu' (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.1 h)))
        (by exact_mod_cast hfac')
      have hgrowth := fib_mul_le_of_le (by norm_num : 2 ≤ 28) h28
      have h28v : Nat.fib 28 = 317811 := by decide
      rw [h28v] at hgrowth
      have hprod : Nat.fib n ≤ u' * (3 * n) := by
        rw [hfac']
        calc 3 ^ a' * u' ≤ (3 * n) * u' := Nat.mul_le_mul_right _ hbound
          _ = u' * (3 * n) := by ring
      have : 317811 ≤ 84 * u' := by
        have hn0 : 0 < n := by omega
        have : 317811 * n ≤ (84 * u') * n := by nlinarith
        exact Nat.le_of_mul_le_mul_right this hn0
      push_cast
      omega

/-- Proposition 5.11 for the representatives: a positive-definite extension
with `c = (0, 0, c₃)`, `0 ≤ c₃ ≤ 2`, that represents 987 is
Fibonacci-universal. -/
theorem fibonacciUniversal_rep (i : FibonacciClassicalInputs) (c₃ m : ℤ)
    (hc : 0 ≤ c₃ ∧ c₃ < 3)
    (hM : (⟨0, 0, c₃, m⟩ : QuaternaryExtension T).PosDef)
    (h987 : (⟨0, 0, c₃, m⟩ : QuaternaryExtension T).Represents 987) :
    (⟨0, 0, c₃, m⟩ : QuaternaryExtension T).FibonacciUniversal := by
  set M : QuaternaryExtension T := ⟨0, 0, c₃, m⟩ with hMdef
  have hT987 := not_represents_truant i.representation
  intro n
  by_cases hT : T.Represents (Nat.fib n)
  · exact M.represents_of_ternary hT
  by_cases hτ : Nat.fib n = 987
  · rw [hτ]
    exact_mod_cast h987
  obtain ⟨hN, a, u, hfac, ho, hu, hns, hu4⟩ := exception_data i n hT hτ
  -- The extension bound `3 m ≤ 3 · 987 + c₃²`.
  have hm := det_mul_m_le det_pos hM h987 hT987
  have hcα : M.cα = c₃ ^ 2 := by
    simp only [hMdef]
    quaternary_norm
    ring
  rw [hcα] at hm
  norm_num [hMdef] at hm
  by_cases hc3 : c₃ = 0
  · -- `c₃ = 0`: `M = T ⊥ ⟨m⟩`, `q = m`.
    subst hc3
    have hq : M.q = m := by simpa using q_rep 0 m hc
    have hq9 : ¬ 9 ∣ m := hq ▸ not_nine_dvd_q i.representation M h987
    have hm0 : 0 < m := hM.m_pos
    have h3N : (3 : ℤ) ∣ Nat.fib n := by
      rw [hfac]
      obtain ⟨j, rfl⟩ := ho
      exact (dvd_pow_self 3 (by omega)).mul_right u
    by_cases h3m : (3 : ℤ) ∣ m
    · -- `m = 3 b` with `3 ∤ b` and `b ≤ 329`: Lemma 5.10.
      obtain ⟨b, rfl⟩ := h3m
      obtain ⟨k, hk⟩ := exists_sub_represents i.representation data a u b ho hfac
        hu hns (hq.trans rfl) (fun ⟨c, hc⟩ => hq9 ⟨c, by rw [hc]; ring⟩)
        (by omega) (by omega)
      exact represents_of_sub det_pos hk
    · -- `3 ∤ m`: subtract `m` once.
      apply represents_of_sub det_pos (k := 1)
      rw [hq]
      have := represents_of_local i.representation data 0 (Nat.fib n - m * 1 ^ 2)
        (by omega) (fun h => h3m (by simpa using (dvd_sub h3N h))) (Or.inl ⟨0, rfl⟩)
      simpa using this
  · -- `c₃ ≠ 0`: `Q(x, y, z, 1) = m + Φ_{3,c₃}(x, y, z)` and Lemma 5.8.
    have hm988 : m ≤ 988 := by
      rcases (by omega : c₃ = 1 ∨ c₃ = 2) with rfl | rfl <;> omega
    obtain ⟨x, y, z, hxyz⟩ := represents_phi i.representation data c₃
      (by omega) (Nat.fib n - m) (by omega)
    refine ⟨x, y, z, 1, ?_⟩
    simp only [hMdef, QuaternaryExtension.eval, diag_eval]
    linear_combination hxyz

/-- Proposition 5.11: every positive-definite quaternary extension of
`⟨1,1,3⟩` that represents its truant `F₁₆ = 987` is Fibonacci-universal. -/
theorem fibonacciUniversal (i : FibonacciClassicalInputs)
    (M : QuaternaryExtension T) (hM : M.PosDef) (h987 : M.Represents 987) :
    M.FibonacciUniversal := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h3, h3'⟩ := exists_rep M
  rw [← fibonacciUniversal_shift_iff M a₁ a₂ a₃]
  have hM' := hM.shift a₁ a₂ a₃
  have h987' := (represents_shift_iff M a₁ a₂ a₃).2 h987
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h3 h3' hM' h987' ⊢
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h3 h3'
  subst h1 h2
  exact fibonacciUniversal_rep i c₃ m ⟨h3, h3'⟩ hM' h987'

end Escalator113

end FibonacciCriterion
