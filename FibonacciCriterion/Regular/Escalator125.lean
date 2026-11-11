import FibonacciCriterion.Regular.OddPrimeTools
import FibonacciCriterion.Forms.QuaternaryExtension
import FibonacciCriterion.Fibonacci.Growth
import FibonacciCriterion.ClassicalInputs.Definitions

/-!
# Fibonacci-universality of extensions of `⟨1,2,5⟩` (Proposition 5.12)

`⟨1,2,5⟩` omits a positive integer exactly when its 5-adic valuation is odd
and its unit part is a nonsquare modulo 5. Its Fibonacci truant is
`F₁₅ = 610`. The proof follows §5.4 of the manuscript.

* `not_represents_sq_mul_truant`: Lemma 3.6 for `⟨1,2,5⟩`.
* `exists_rep`: the representatives `c = (0, c₂, c₃)`, `c₂ ∈ {0, 1}`,
  `c₃ ∈ {-2, …, 2}` of §4.1.
* `not_twentyfive_dvd_q`: Lemma 4.3 for `⟨1,2,5⟩`, `v₅(q) ≤ 1`.
* `obstructed_index`: a Fibonacci member of the exceptional set has index 15,
  20, or at least 25.
* `exception_data`: every later Fibonacci exception is at least `F₂₀`; after
  `F₂₀ = 5 · 1353` the unit part exceeds `4 · 488` by the bound (1) and
  Lemma 2.1 with the cutoff `F₂₅ / 25`.
* `fibonacciUniversal`: Proposition 5.12.
* `represents_fib_below_fifteen`: `⟨1,2,5⟩` represents `Fₙ` for `n < 15` (the
  truant column of Figure 1), used in `Escalation.TernaryTruants`.
-/

namespace FibonacciCriterion

namespace Escalator125

open OddPrime TernaryGram QuaternaryExtension

/-- The escalator `⟨1,2,5⟩`. -/
abbrev T : TernaryGram := diag 1 2 5

theorem data : IsData 5 2 := Or.inr ⟨rfl, rfl⟩

theorem det_pos : 0 < T.det := by norm_num

theorem posDef : T.PosDef := diag_posDef (by norm_num) (by norm_num) (by norm_num)

/-- The unit part 122 of the truant `610 = 5 · 122` is a nonsquare modulo 5
(Lemma 2.4). -/
theorem truant_not_square : ¬ IsSquareMod 5 122 := by
  rw [isSquareMod_five]
  norm_num

/-- Lemma 3.6 for `⟨1,2,5⟩`: it omits every nonzero square multiple of its
truant `610 = 5 · 122`. -/
theorem not_represents_sq_mul_truant (i : ClassicalInputs) (k : ℤ) (hk : k ≠ 0) :
    ¬ T.Represents (k ^ 2 * 610) := by
  have := not_represents_sq_mul i data 1 122 (by norm_num) odd_one
    truant_not_square k hk
  simpa using this

/-- Lemma 3.6 with `k = 1`: `⟨1,2,5⟩` omits its truant 610. -/
theorem not_represents_truant (i : ClassicalInputs) : ¬ T.Represents 610 := by
  simpa using not_represents_sq_mul_truant i 1 one_ne_zero

/-- The representatives of §4.1 for `⟨1,2,5⟩`: after a change of generator,
`c = (0, c₂, c₃)` with `c₂ ∈ {0, 1}` and `-2 ≤ c₃ ≤ 2`. -/
theorem exists_rep (M : QuaternaryExtension T) :
    ∃ a₁ a₂ a₃ : ℤ, (M.shift a₁ a₂ a₃).c₁ = 0 ∧
      0 ≤ (M.shift a₁ a₂ a₃).c₂ ∧ (M.shift a₁ a₂ a₃).c₂ < 2 ∧
      -2 ≤ (M.shift a₁ a₂ a₃).c₃ ∧ (M.shift a₁ a₂ a₃).c₃ ≤ 2 := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h2', h3, h3'⟩ :=
    exists_shift_diag (B := 2) (C := 5) (by norm_num) (by norm_num) 0 (-2) M
  exact ⟨a₁, a₂, a₃, h1, by omega, by omega, by omega, by omega⟩

/-- The value of `q` for the representatives `c = (0, c₂, c₃)`, according as
`c₂ = 0` or `c₂ = 1`: `q = m` or `4 m - 2` when `c₃ = 0` (`d = 1, 2`);
`q = 25 m - 5 c₃²` or `100 m - 50 - 20 c₃²` when `c₃ ≠ 0` (`d = 5, 10`). -/
theorem q_rep (c₂ c₃ m : ℤ) (h2 : c₂ = 0 ∨ c₂ = 1) (h3 : -2 ≤ c₃ ∧ c₃ ≤ 2) :
    (⟨0, c₂, c₃, m⟩ : QuaternaryExtension T).q =
      if c₃ = 0 then (if c₂ = 0 then m else 4 * m - 2)
      else (if c₂ = 0 then 25 * m - 5 * c₃ ^ 2 else 100 * m - 50 - 20 * c₃ ^ 2) := by
  rcases h2 with rfl | rfl <;>
    rcases (by omega : c₃ = -2 ∨ c₃ = -1 ∨ c₃ = 0 ∨ c₃ = 1 ∨ c₃ = 2) with
      rfl | rfl | rfl | rfl | rfl <;>
    quaternary_norm <;> ring

theorem cα_rep (c₂ c₃ m : ℤ) :
    (⟨0, c₂, c₃, m⟩ : QuaternaryExtension T).cα = 5 * c₂ ^ 2 + 2 * c₃ ^ 2 := by
  quaternary_norm
  ring

/-- Lemma 4.3 for `⟨1,2,5⟩`: an extension representing 610 has
`v₅(q) ≤ 1`. -/
theorem not_twentyfive_dvd_q (i : ClassicalInputs) (M : QuaternaryExtension T)
    (h610 : M.Represents 610) : ¬ 25 ∣ M.q := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h2', h3, h3'⟩ := exists_rep M
  rw [← q_shift det_pos M a₁ a₂ a₃]
  have h610' := (represents_shift_iff M a₁ a₂ a₃).2 h610
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h2' h3 h3' h610'
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h2' h3 h3'
  subst h1
  have hc₂ : c₂ = 0 ∨ c₂ = 1 := by omega
  rw [q_rep c₂ c₃ m hc₂ ⟨h3, h3'⟩]
  split_ifs with hc3 hc2 hc2
  · -- `c = 0`: `M = T ⊥ ⟨m⟩`, and `610 - m w²` would be obstructed.
    subst hc3 hc2
    rintro ⟨s, rfl⟩
    obtain ⟨x, y, z, w, hxyzw⟩ := h610'
    have hrep : T.Represents (5 ^ 1 * (122 - 5 * (s * w ^ 2))) := by
      refine ⟨x, y, z, ?_⟩
      simp only [QuaternaryExtension.eval, diag_eval] at hxyzw ⊢
      linear_combination hxyzw
    generalize s * w ^ 2 = t at hrep
    exact not_represents_of_local i data 1 (122 - 5 * t) (by omega) odd_one
      ((isSquareMod_five _).not.2 (by omega)) hrep
  · -- `c = (0, 1, 0)`, `d = 2`: the scaled inclusion
    -- `4 Q(x,y,z,w) = (2x)² + 2(2y + w)² + 5(2z)² + q w²`.
    subst hc3
    have hc2' : c₂ = 1 := by omega
    subst hc2'
    rintro ⟨s, hs⟩
    obtain ⟨x, y, z, w, hxyzw⟩ := h610'
    have hrep : T.Represents (5 ^ 1 * (488 - 5 * (s * w ^ 2))) := by
      refine ⟨2 * x, 2 * y + w, 2 * z, ?_⟩
      simp only [QuaternaryExtension.eval, diag_eval] at hxyzw ⊢
      linear_combination 4 * hxyzw - w ^ 2 * hs
    generalize s * w ^ 2 = t at hrep
    exact not_represents_of_local i data 1 (488 - 5 * t) (by omega) odd_one
      ((isSquareMod_five _).not.2 (by omega)) hrep
  · -- `c₃ ≠ 0`, `c₂ = 0`: `q = 25 m - 5 c₃²` has valuation 1.
    rcases (by omega : c₃ = -2 ∨ c₃ = -1 ∨ c₃ = 1 ∨ c₃ = 2) with
      rfl | rfl | rfl | rfl <;> omega
  · -- `c₃ ≠ 0`, `c₂ = 1`: `q = 100 m - 50 - 20 c₃²` has valuation 1.
    rcases (by omega : c₃ = -2 ∨ c₃ = -1 ∨ c₃ = 1 ∨ c₃ = 2) with
      rfl | rfl | rfl | rfl <;> omega

/-- A Fibonacci member of the exceptional set of `⟨1,2,5⟩` has index 15, 20,
or at least 25 (Lemma 2.4 and the proof of Proposition 5.12): its index is
divisible by 5, and `F₅ = 5 · 1`, `F₁₀ = 5 · 11` have square unit parts. -/
theorem obstructed_index (n a : ℕ) (u : ℤ) (hfac : (Nat.fib n : ℤ) = 5 ^ a * u)
    (hu : ¬ 5 ∣ u) (ho : Odd a) (hns : ¬ IsSquareMod 5 u) :
    n = 15 ∨ n = 20 ∨ 25 ≤ n := by
  have h5 : 5 ∣ Nat.fib n := by
    have : (5 : ℤ) ∣ Nat.fib n := by
      rw [hfac]
      obtain ⟨j, rfl⟩ := ho
      exact (dvd_pow_self 5 (by omega)).mul_right u
    exact_mod_cast this
  have h5n : 5 ∣ n := (five_dvd_fib_iff n).1 h5
  have pin : ∀ (e : ℕ) (v : ℤ), ¬ 5 ∣ v → (Nat.fib n : ℤ) = 5 ^ e * v →
      e = a ∧ v = u := fun e v hv he =>
    normalization_unique (by norm_num) hv hu (he.symm.trans hfac)
  obtain ⟨j, rfl⟩ := h5n
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ 5 ≤ j) with
    rfl | rfl | rfl | rfl | rfl | hj
  · simp at hfac
    exact absurd (hfac ▸ dvd_zero 5) hu
  · obtain ⟨-, rfl⟩ := pin 1 1 (by norm_num) (by decide)
    exact absurd ((isSquareMod_five _).2 (by norm_num)) hns
  · obtain ⟨-, rfl⟩ := pin 1 11 (by norm_num) (by decide)
    exact absurd ((isSquareMod_five _).2 (by norm_num)) hns
  · left; rfl
  · right; left; rfl
  · right; right; omega

/-- Proposition 3.2 for `⟨1,2,5⟩`, truant column: `⟨1,2,5⟩` represents `Fₙ`
for every `n < 15`, by Lemma 2.4. -/
theorem represents_fib_below_fifteen (i : ClassicalInputs) (n : ℕ) (hn : n < 15) :
    T.Represents (Nat.fib n) := by
  by_contra hT
  have hob := (not_congr (represents_iff i data
    (show (0 : ℤ) ≤ Nat.fib n by positivity))).1 hT
  rw [not_not] at hob
  obtain ⟨a, u, hfac, hu, ho, hns⟩ := hob
  rcases obstructed_index n a u hfac hu ho hns with h | h | h <;> omega

/-- Every Fibonacci exception `Fₙ ≠ 610` of `⟨1,2,5⟩` is at least
`F₂₀ = 6765` and has the form `5^a u` with `a` odd and `u` a nonsquare modulo
5; either `Fₙ = F₂₀ = 5 · 1353`, or `u > 4 · 488`. Its index is divisible by
5; after `F₂₀` it is at least 25, and the bound `5^{v₅(Fₙ)} ≤ n` with
Lemma 2.1 gives `u ≥ Fₙ / n ≥ F₂₅ / 25`. -/
theorem exception_data (i : FibonacciClassicalInputs) (n : ℕ)
    (hn : ¬ T.Represents (Nat.fib n)) (h610 : Nat.fib n ≠ 610) :
    6765 ≤ Nat.fib n ∧ ∃ (a : ℕ) (u : ℤ), (Nat.fib n : ℤ) = 5 ^ a * u ∧
      Odd a ∧ ¬ 5 ∣ u ∧ ¬ IsSquareMod 5 u ∧
      ((Nat.fib n = 6765 ∧ a = 1 ∧ u = 1353) ∨ 4 * 488 < u) := by
  have hob := (not_congr (represents_iff i.representation data
    (show (0 : ℤ) ≤ Nat.fib n by positivity))).1 hn
  rw [not_not] at hob
  obtain ⟨a, u, hfac, hu, ho, hns⟩ := hob
  have pin : ∀ (e : ℕ) (v : ℤ), ¬ 5 ∣ v → (Nat.fib n : ℤ) = 5 ^ e * v →
      e = a ∧ v = u := fun e v hv he =>
    normalization_unique (by norm_num) hv hu (he.symm.trans hfac)
  have hsmall : n = 20 ∨ 25 ≤ n := by
    rcases obstructed_index n a u hfac hu ho hns with rfl | h | h
    · exact absurd (by decide) h610
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨?_, a, u, hfac, ho, hu, hns, ?_⟩
  · rcases hsmall with rfl | h
    · decide
    · calc 6765 ≤ Nat.fib 25 := by decide
        _ ≤ Nat.fib n := Nat.fib_mono h
  · rcases hsmall with rfl | h25
    · obtain ⟨rfl, rfl⟩ := pin 1 1353 (by norm_num) (by decide)
      exact Or.inl ⟨by decide, rfl, rfl⟩
    · right
      obtain ⟨a', u', hfac', hu', hbound⟩ :=
        FibonacciValuationInputs.five_prime_power_bound i.valuations n (by omega)
      obtain ⟨rfl, rfl⟩ := pin a' u'
        (fun h => hu' (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.1 h)))
        (by exact_mod_cast hfac')
      have hgrowth := fib_mul_le_of_le (by norm_num : 2 ≤ 25) h25
      have h25v : Nat.fib 25 = 75025 := by decide
      rw [h25v] at hgrowth
      have hprod : Nat.fib n ≤ u' * n := by
        rw [hfac']
        calc 5 ^ a' * u' ≤ n * u' := Nat.mul_le_mul_right _ hbound
          _ = u' * n := by ring
      have : 75025 ≤ 25 * u' := by
        have hn0 : 0 < n := by omega
        have : 75025 * n ≤ (25 * u') * n := by nlinarith
        exact Nat.le_of_mul_le_mul_right this hn0
      push_cast
      omega

/-- Proposition 5.12 for the representatives: a positive-definite extension
with `c = (0, c₂, c₃)`, `c₂ ∈ {0, 1}`, `-2 ≤ c₃ ≤ 2`, that represents 610 is
Fibonacci-universal. -/
theorem fibonacciUniversal_rep (i : FibonacciClassicalInputs) (c₂ c₃ m : ℤ)
    (hc₂ : c₂ = 0 ∨ c₂ = 1) (hc₃ : -2 ≤ c₃ ∧ c₃ ≤ 2)
    (hM : (⟨0, c₂, c₃, m⟩ : QuaternaryExtension T).PosDef)
    (h610 : (⟨0, c₂, c₃, m⟩ : QuaternaryExtension T).Represents 610) :
    (⟨0, c₂, c₃, m⟩ : QuaternaryExtension T).FibonacciUniversal := by
  set M : QuaternaryExtension T := ⟨0, c₂, c₃, m⟩ with hMdef
  have hT610 := not_represents_truant i.representation
  intro n
  by_cases hT : T.Represents (Nat.fib n)
  · exact M.represents_of_ternary hT
  by_cases hτ : Nat.fib n = 610
  · rw [hτ]
    exact_mod_cast h610
  obtain ⟨hN, a, u, hfac, ho, hu, hns, hu4⟩ := exception_data i n hT hτ
  -- The extension bound `10 m ≤ 10 · 610 + 5 c₂² + 2 c₃²`.
  have hm := det_mul_m_le det_pos hM h610 hT610
  rw [hMdef, cα_rep] at hm
  norm_num at hm
  have hm0 : 0 < m := hM.m_pos
  by_cases hc3 : c₃ = 0
  · -- `c₃ = 0`: the orthogonal vector has `q = m` or `q = 4 m - 2`.
    subst hc3
    have hq : M.q = if c₂ = 0 then m else 4 * m - 2 := by
      rw [hMdef, q_rep c₂ 0 m hc₂ ⟨by norm_num, by norm_num⟩]
      simp
    have hq25 : ¬ 25 ∣ M.q := not_twentyfive_dvd_q i.representation M h610
    have hqpos : 0 < M.q := q_pos det_pos hM
    have hqlt : M.q < 2440 := by
      rw [hq]
      rcases hc₂ with rfl | rfl <;> norm_num at hm ⊢ <;> omega
    have h5N : (5 : ℤ) ∣ Nat.fib n := by
      rw [hfac]
      obtain ⟨j, rfl⟩ := ho
      exact (dvd_pow_self 5 (by omega)).mul_right u
    by_cases h5q : (5 : ℤ) ∣ M.q
    · obtain ⟨b, hb⟩ := h5q
      have hb5 : ¬ 5 ∣ b := fun ⟨c, hc⟩ => hq25 ⟨c, by rw [hb, hc]; ring⟩
      by_cases hub : 4 * b < u
      · -- Lemma 5.10.
        obtain ⟨k, hk⟩ := exists_sub_represents i.representation data a u b ho
          hfac hu hns hb hb5 (by omega) hub
        exact represents_of_sub det_pos hk
      · -- Only `N = F₂₀` with `338 < b < 488` remains.
        rcases hu4 with ⟨hF20, rfl, rfl⟩ | hu4
        swap
        · omega
        -- Here `c₂ = 1`, `q = 4 m - 2 = 5 b`, and `b ≡ 2 (mod 4)`.
        have hc2 : c₂ = 1 := by
          rcases hc₂ with rfl | rfl
          · simp at hq
            norm_num at hm
            omega
          · rfl
        subst hc2
        simp only [one_ne_zero, ite_false] at hq
        have hb4 : b % 4 = 2 := by omega
        -- The truant representation forces `w = ±1`, so `T` represents
        -- `2440 - q = 5 (488 - b)`.
        obtain ⟨x, y, z, w, hxyzw⟩ := h610
        have h4Q : (2 * x) ^ 2 + 2 * (2 * y + w) ^ 2 + 5 * (2 * z) ^ 2 + M.q * w ^ 2 =
            2440 := by
          rw [hq]
          simp only [QuaternaryExtension.eval, diag_eval] at hxyzw
          linear_combination 4 * hxyzw
        have hw : w ≠ 0 := by
          rintro rfl
          exact hT610 ⟨x, y, z, by simpa [QuaternaryExtension.eval] using hxyzw⟩
        have hw1 : w ^ 2 = 1 := by
          have h1 : 1 ≤ w ^ 2 := by
            have : 0 < w ^ 2 := by positivity
            omega
          have : M.q * w ^ 2 ≤ 2440 := by
            nlinarith [sq_nonneg (2 * x), sq_nonneg (2 * y + w), sq_nonneg (2 * z)]
          nlinarith
        have hrep : T.Represents (5 ^ 1 * (488 - b)) :=
          ⟨2 * x, 2 * y + w, 2 * z, by
            simp only [diag_eval]
            rw [hw1, hb] at h4Q
            linear_combination h4Q⟩
        have hb1 : b % 5 ≠ 1 := by
          intro hb1
          exact not_represents_of_local i.representation data 1 (488 - b)
            (by omega) odd_one ((isSquareMod_five _).not.2 (by omega)) hrep
        -- Take `k = 1`: `R = 6765 - 5 b = 5 (1353 - b)` is represented.
        apply represents_of_sub det_pos (k := 1)
        rw [hb, hfac]
        have hb' : b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
        rcases hb' with h2 | h3 | h4
        · have := represents_of_local i.representation data 1 (1353 - b) (by omega)
            (by omega) (Or.inr ((isSquareMod_five _).2 (by omega)))
          convert this using 1
          ring
        · by_cases h25 : b % 25 = 3
          · have hb : b = 378 ∨ b = 478 := by omega
            rcases hb with rfl | rfl
            · have := represents_of_local i.representation data 3 39 (by norm_num)
                (by norm_num) (Or.inr ((isSquareMod_five _).2 (by norm_num)))
              convert this using 1
              norm_num
            · have := represents_of_local i.representation data 4 7 (by norm_num)
                (by norm_num) (Or.inl ⟨2, rfl⟩)
              convert this using 1
              norm_num
          · have := represents_of_local i.representation data 2 ((1353 - b) / 5)
              (by omega) (by omega) (Or.inl ⟨1, rfl⟩)
            convert this using 1
            omega
        · have := represents_of_local i.representation data 1 (1353 - b) (by omega)
            (by omega) (Or.inr ((isSquareMod_five _).2 (by omega)))
          convert this using 1
          ring
    · -- `5 ∤ q`: subtract `q` once.
      apply represents_of_sub det_pos (k := 1)
      have := represents_of_local i.representation data 0 (Nat.fib n - M.q * 1 ^ 2)
        (by nlinarith) (fun h => h5q (by simpa using (dvd_sub h5N h)))
        (Or.inl ⟨0, rfl⟩)
      simpa using this
  · -- `c₃ ≠ 0`: `Q(x, y, z, 2) = Φ_{5,2c₃}(x, y + c₂, z) + 4 m - 2 c₂²` and
    -- Lemma 5.8.
    have hm611 : m ≤ 611 := by
      rcases hc₂ with rfl | rfl <;>
        rcases (by omega : c₃ = -2 ∨ c₃ = -1 ∨ c₃ = 1 ∨ c₃ = 2) with
          rfl | rfl | rfl | rfl <;> omega
    have hc22 : c₂ ^ 2 ≤ 1 := by rcases hc₂ with rfl | rfl <;> norm_num
    obtain ⟨x, y, z, hxyz⟩ := represents_phi i.representation data (2 * c₃)
      (by omega) (Nat.fib n - (4 * m - 2 * c₂ ^ 2)) (by nlinarith)
    refine ⟨x, y - c₂, z, 2, ?_⟩
    simp only [hMdef, QuaternaryExtension.eval, diag_eval]
    linear_combination hxyz

/-- Proposition 5.12: every positive-definite quaternary extension of
`⟨1,2,5⟩` that represents its truant `F₁₅ = 610` is Fibonacci-universal. -/
theorem fibonacciUniversal (i : FibonacciClassicalInputs)
    (M : QuaternaryExtension T) (hM : M.PosDef) (h610 : M.Represents 610) :
    M.FibonacciUniversal := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h2', h3, h3'⟩ := exists_rep M
  rw [← fibonacciUniversal_shift_iff M a₁ a₂ a₃]
  have hM' := hM.shift a₁ a₂ a₃
  have h610' := (represents_shift_iff M a₁ a₂ a₃).2 h610
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h2' h3 h3' hM' h610' ⊢
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h2' h3 h3'
  subst h1
  exact fibonacciUniversal_rep i c₂ c₃ m (by omega) ⟨h3, h3'⟩ hM' h610'

end Escalator125

end FibonacciCriterion
