import FibonacciCriterion.Forms.QuaternaryExtension
import FibonacciCriterion.Irregular.LargeIndices
import FibonacciCriterion.Irregular.InitialWindow
import FibonacciCriterion.Arithmetic.PrimePowerNormalization

/-!
# The irregular escalator `f` (Lemma 4.4, Proposition 6.1)

The form `f` with Gram matrix `[[1,0,0],[0,2,1],[0,1,4]]` has determinant 7
and Fibonacci truant `F₈ = 21`. `not_representsF_obstructed` is the 7-adic
obstruction of Proposition 3.3: `f` omits `7^{2a+1} u` with `u` a nonsquare
modulo 7, proven by 7-adic descent. It gives Lemma 3.6 for `f`
(`not_represents_sq_mul_truant`).

For quaternary extensions of `f`, `exists_rep` gives the representatives
`c = (0, 0, c₃)` with `0 ≤ c₃ ≤ 6` of §4.1, `q_mem_coefficients` is
Lemma 4.4 (`q ∈ Q₇`), and `fibonacciUniversal` is Proposition 6.1.
-/

namespace FibonacciCriterion

namespace EscalatorF

open Irregular TernaryGram QuaternaryExtension

/-- The escalator `f` as a `TernaryGram`: the matrix `fGram`, whose form is `f`
(`fGram_eval`, `fGram_represents_iff`). -/
abbrev T : TernaryGram := fGram

/-- `f` has determinant 7. -/
theorem det_eq : T.det = 7 := by decide

/-- The determinant of `f` is positive. -/
theorem det_pos : 0 < T.det := by rw [det_eq]; norm_num

/-- `f` is positive definite: `2f = 2x² + (2y + z)² + 7z²`. -/
theorem posDef : T.PosDef := by
  intro x y z h
  have e : 2 * T.eval x y z = 2 * x ^ 2 + (2 * y + z) ^ 2 + 7 * z ^ 2 := by
    simp only [TernaryGram.eval]
    ring
  have : 0 < 2 * T.eval x y z := by
    rw [e]
    by_cases hz : z = 0
    · subst hz
      by_cases hx : x = 0
      · subst hx
        have hy : y ≠ 0 := fun hy => h ⟨rfl, hy, rfl⟩
        have := pow_pos (abs_pos.2 hy) 2
        rw [sq_abs] at this
        nlinarith
      · have := pow_pos (abs_pos.2 hx) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg (2 * y)]
    · have := pow_pos (abs_pos.2 hz) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg x, sq_nonneg (2 * y + z)]
  linarith

/-! ### The 7-adic obstruction and Lemma 3.6 -/

/-- If `2x² + Y² ≡ 0 (mod 7)`, then `7 ∣ x` and `7 ∣ Y` (-2 is a nonsquare
modulo 7). -/
theorem seven_dvd_of_two_sq_add_sq (x Y : ℤ) (h : (7 : ℤ) ∣ 2 * x ^ 2 + Y ^ 2) :
    (7 : ℤ) ∣ x ∧ (7 : ℤ) ∣ Y := by
  have key : ∀ a b : ZMod 7, 2 * a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * x ^ 2 + Y ^ 2) 7).2
    (by exact_mod_cast h)
  push_cast at hz
  obtain ⟨hx, hY⟩ := key x Y hz
  exact ⟨by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd x 7).1 hx,
    by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd Y 7).1 hY⟩

/-- If `7 ∣ z²`, then `7 ∣ z`. -/
theorem seven_dvd_of_seven_dvd_sq (z : ℤ) (h : (7 : ℤ) ∣ z ^ 2) : (7 : ℤ) ∣ z :=
  (Int.prime_iff_natAbs_prime.2 (by norm_num)).dvd_of_dvd_pow h

/-- The 7-adic obstruction of `f` (part of Proposition 3.3): `f` omits every
`7^{2a+1} u` with `u ≡ 3, 5, 6 (mod 7)`. -/
theorem not_representsF_obstructed (a : ℕ) (u : ℤ)
    (hu : u % 7 = 3 ∨ u % 7 = 5 ∨ u % 7 = 6) : ¬ RepresentsF (7 ^ (2 * a + 1) * u) := by
  have h7 : (7 : ℤ) ≠ 0 := by norm_num
  induction a with
  | zero =>
    rintro ⟨x, y, z, h⟩
    have h2 : 2 * x ^ 2 + (2 * y + z) ^ 2 + 7 * z ^ 2 = 14 * u := by
      simp only [f] at h
      linear_combination 2 * h
    obtain ⟨⟨x', rfl⟩, ⟨Y, hY⟩⟩ := seven_dvd_of_two_sq_add_sq x (2 * y + z)
      ⟨2 * u - z ^ 2, by linear_combination h2⟩
    rw [hY] at h2
    have h3 : 14 * x' ^ 2 + 7 * Y ^ 2 + z ^ 2 = 2 * u :=
      mul_left_cancel₀ h7 (by linear_combination h2)
    -- `z² ≡ 2u (mod 7)`, so `u ≡ 4z²` is a square modulo 7.
    have hz : (7 : ℤ) ∣ z ^ 2 - 2 * u := ⟨-(2 * x' ^ 2 + Y ^ 2), by linear_combination h3⟩
    have key : ∀ a b : ZMod 7, a ^ 2 = 2 * b → b ≠ 3 ∧ b ≠ 5 ∧ b ≠ 6 := by decide
    have hzz := (ZMod.intCast_eq_intCast_iff_dvd_sub (2 * u) (z ^ 2) 7).2
      (by exact_mod_cast hz)
    push_cast at hzz
    obtain ⟨h3', h5, h6⟩ := key z u hzz.symm
    have hu' : ((u % 7 : ℤ) : ZMod 7) = (u : ZMod 7) := ZMod.intCast_mod u 7
    rcases hu with h | h | h <;> rw [h] at hu' <;> push_cast at hu'
    · exact h3' hu'.symm
    · exact h5 hu'.symm
    · exact h6 hu'.symm
  | succ a ih =>
    rintro ⟨x, y, z, h⟩
    have hp : (7 : ℤ) ^ (2 * (a + 1) + 1) = 7 ^ (2 * a + 1) * 49 := by
      rw [show 2 * (a + 1) + 1 = (2 * a + 1) + 2 by ring, pow_add]
      norm_num
    rw [hp] at h
    have h2 : 2 * x ^ 2 + (2 * y + z) ^ 2 + 7 * z ^ 2 = 98 * (7 ^ (2 * a + 1) * u) := by
      simp only [f] at h
      linear_combination 2 * h
    obtain ⟨⟨x', rfl⟩, ⟨Y, hY⟩⟩ := seven_dvd_of_two_sq_add_sq x (2 * y + z)
      ⟨14 * (7 ^ (2 * a + 1) * u) - z ^ 2, by linear_combination h2⟩
    rw [hY] at h2
    have h3 : 14 * x' ^ 2 + 7 * Y ^ 2 + z ^ 2 = 14 * (7 ^ (2 * a + 1) * u) :=
      mul_left_cancel₀ h7 (by linear_combination h2)
    obtain ⟨z', rfl⟩ := seven_dvd_of_seven_dvd_sq z
      ⟨2 * (7 ^ (2 * a + 1) * u) - 2 * x' ^ 2 - Y ^ 2, by linear_combination h3⟩
    obtain ⟨y', rfl⟩ : (7 : ℤ) ∣ y := by
      have : (7 : ℤ) ∣ 2 * y := ⟨Y - z', by linear_combination hY⟩
      exact ((Int.prime_iff_natAbs_prime.2 (by norm_num) : Prime (7 : ℤ)).dvd_or_dvd
        this).resolve_left (by norm_num)
    apply ih
    refine ⟨x', y', z', ?_⟩
    simp only [f] at h ⊢
    exact mul_left_cancel₀ (show (49 : ℤ) ≠ 0 by norm_num) (by linear_combination h)

/-- Lemma 3.6 for `f`: `f` omits `k² · 21` for every `k ≠ 0`. -/
theorem not_represents_sq_mul_truant (k : ℤ) (hk : k ≠ 0) :
    ¬ T.Represents (k ^ 2 * 21) := by
  rw [fGram_represents_iff]
  obtain ⟨s, ω, rfl, hω⟩ := exists_pow_mul_not_dvd 7 (by norm_num) k hk
  push_cast at hω ⊢
  have hfac : ((7 : ℤ) ^ s * ω) ^ 2 * 21 = 7 ^ (2 * s + 1) * (3 * ω ^ 2) := by
    rw [pow_succ (7 : ℤ) (2 * s), mul_comm 2 s, pow_mul]
    ring
  rw [hfac]
  apply not_representsF_obstructed
  have : ω % 7 = 1 ∨ ω % 7 = 2 ∨ ω % 7 = 3 ∨ ω % 7 = 4 ∨ ω % 7 = 5 ∨ ω % 7 = 6 := by
    omega
  rcases this with h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

/-- `f` omits its truant `F₈ = 21` (Proposition 3.5): Lemma 3.6 with `k = 1`. -/
theorem not_represents_truant : ¬ T.Represents 21 := by
  simpa using not_represents_sq_mul_truant 1 one_ne_zero

/-- The form `f` omits 7 (§3.3). Since 7 is not locally obstructed, the proof
bounds the coordinates and checks every vector within the bounds. -/
theorem not_representsF_seven : ¬ RepresentsF (7 : ℤ) := by
  rintro ⟨x, y, z, hxyz⟩
  unfold f at hxyz
  have hx : x ^ 2 ≤ 7 := by nlinarith [sq_nonneg y, sq_nonneg (y + z), sq_nonneg z]
  have hy : y ^ 2 ≤ 7 := by nlinarith [sq_nonneg x, sq_nonneg (y + z), sq_nonneg z]
  have hz : z ^ 2 ≤ 2 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (y + z)]
  have hx1 : x ≤ 2 := by nlinarith
  have hx2 : -2 ≤ x := by nlinarith
  have hy1 : y ≤ 2 := by nlinarith
  have hy2 : -2 ≤ y := by nlinarith
  have hz1 : z ≤ 1 := by nlinarith
  have hz2 : -1 ≤ z := by nlinarith
  interval_cases x <;> interval_cases y <;> interval_cases z <;> norm_num at hxyz

/-! ### Representatives and Lemma 4.4 -/

/-- The representatives of §4.1: a change of generator brings `c` to
`(0, 0, c₃)` with `0 ≤ c₃ ≤ 6`. -/
theorem exists_rep (M : QuaternaryExtension T) :
    ∃ a₁ a₂ a₃ : ℤ, (M.shift a₁ a₂ a₃).c₁ = 0 ∧ (M.shift a₁ a₂ a₃).c₂ = 0 ∧
      0 ≤ (M.shift a₁ a₂ a₃).c₃ ∧ (M.shift a₁ a₂ a₃).c₃ < 7 := by
  set a₂ := (M.c₃ - 4 * M.c₂) / 7
  refine ⟨-M.c₁, a₂, -M.c₂ - 2 * a₂, ?_, ?_, ?_, ?_⟩ <;>
    simp only [shift, TernaryGram.mul₁, TernaryGram.mul₂, TernaryGram.mul₃] <;>
    omega

/-- `q` for the representatives: `q = m` if `c₃ = 0` (`d = 1`), and
`q = 49 m - 14 c₃²` (`d = 7`) otherwise. -/
theorem q_rep (c₃ m : ℤ) (hc : 0 ≤ c₃ ∧ c₃ < 7) :
    (⟨0, 0, c₃, m⟩ : QuaternaryExtension T).q =
      if c₃ = 0 then m else 49 * m - 14 * c₃ ^ 2 := by
  rcases (by omega : c₃ = 0 ∨ c₃ = 1 ∨ c₃ = 2 ∨ c₃ = 3 ∨ c₃ = 4 ∨ c₃ = 5 ∨
    c₃ = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> quaternary_norm <;> ring

/-- The cases of Lemma 4.4 for a positive-definite extension of `f`
representing 21, read off from the representatives: either `c₃ = 0` and
`q = m` with `0 < m ≤ 21` and `m ≠ 14`, or `c₃ ≠ 0` and `q = 7s`
with `s = 7m - 2c₃² > 0` and `s ≡ 3, 5, 6 (mod 7)`. -/
theorem q_cases (M : QuaternaryExtension T) (hM : M.PosDef) (h21 : M.Represents 21) :
    (0 < M.q ∧ M.q ≤ 21 ∧ M.q ≠ 14) ∨
      ∃ s : ℤ, M.q = 7 * s ∧ 0 < s ∧ (s % 7 = 3 ∨ s % 7 = 5 ∨ s % 7 = 6) := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h3, h3'⟩ := exists_rep M
  rw [← q_shift det_pos M a₁ a₂ a₃]
  have h21' := (represents_shift_iff M a₁ a₂ a₃).2 h21
  have hM' := hM.shift a₁ a₂ a₃
  have hpos := q_pos det_pos hM'
  have hb := q_le_index_sq_mul det_pos hM' h21' not_represents_truant
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h3 h3' h21' hM' hpos hb
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h3 h3'
  subst h1 h2
  have hq := q_rep c₃ m ⟨h3, h3'⟩
  by_cases hc : c₃ = 0
  · -- `c₃ = 0`: `d = 1`, `q = m`, and `M = f ⊥ ⟨m⟩`.
    subst hc
    simp only [ite_true] at hq
    have hd : (⟨0, 0, 0, m⟩ : QuaternaryExtension T).index = 1 := by quaternary_norm
    rw [hd] at hb
    rw [hq] at hpos hb ⊢
    obtain ⟨x, y, z, w, hxyzw⟩ := h21'
    simp only [QuaternaryExtension.eval] at hxyzw
    rw [fGram_eval] at hxyzw
    refine Or.inl ⟨hpos, by linarith, ?_⟩
    -- `q = 14` would force `f` to represent 21 or 7.
    rintro rfl
    have hf := posDef.eval_nonneg x y z
    rw [fGram_eval] at hf
    have hw : w ^ 2 ≤ 1 := by nlinarith
    rcases (by have := sq_nonneg w; omega : w ^ 2 = 0 ∨ w ^ 2 = 1) with h0 | h1
    · exact not_represents_truant ⟨x, y, z, by rw [fGram_eval]; linear_combination hxyzw - 14 * h0⟩
    · exact not_representsF_seven ⟨x, y, z, by linear_combination hxyzw - 14 * h1⟩
  · -- `c₃ ≠ 0`: `d = 7`, `q = 7 (7 m - 2 c₃²)`.
    simp only [hc, ite_false] at hq
    right
    refine ⟨7 * m - 2 * c₃ ^ 2, by rw [hq]; ring, by omega, ?_⟩
    rcases (by omega : c₃ = 1 ∨ c₃ = 2 ∨ c₃ = 3 ∨ c₃ = 4 ∨ c₃ = 5 ∨ c₃ = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Lemma 4.4: every positive-definite extension of `f` representing 21 has
`q ∈ Q₇` (`irregularCoefficients`), and by Lemma 4.1 it contains `f ⊥ ⟨q⟩`.
For `q = 7s`, the bound (5), `q ≤ 21 · 7²`, gives `s ≤ 147`. -/
theorem q_mem_coefficients (M : QuaternaryExtension T) (hM : M.PosDef)
    (h21 : M.Represents 21) :
    0 < M.q ∧ M.q.toNat ∈ irregularCoefficients := by
  have hpos := q_pos det_pos hM
  -- `q ≤ 21 · 7²` is the bound (5).
  have hb5 := q_le_det_sq_mul det_pos hM h21 not_represents_truant
  rw [det_eq] at hb5
  have h147 : M.q ≤ 7 * 147 := by omega
  refine ⟨hpos, ?_⟩
  rcases q_cases M hM h21 with ⟨-, hle, h14⟩ | ⟨s, hs, hs0, hres⟩
  · exact mem_irregularCoefficients_of_le_21 (by omega) (by omega) (by omega)
  · rw [hs, show (7 * s).toNat = 7 * s.toNat by omega]
    exact mem_irregularCoefficients_of_seven_mul (by omega) (by omega)

/-! ### Proposition 6.1 -/

/-- Proposition 6.1: every positive-definite quaternary extension of `f`
representing its truant 21 is Fibonacci-universal. By Lemma 4.4 it contains
`f ⊥ ⟨q⟩` with `q ∈ Q₇`; Proposition 3.5 gives `Fₙ` for `n < 48` other than
`F₈ = 21`, and §§6.1–6.3 (`representsFPlus_fib_of_forty_eight_le`) give every `n ≥ 48`.
The hypothesis `hclass` is the sufficiency direction of Proposition 3.3. -/
theorem fibonacciUniversal
    (hclass : ∀ t : ℕ, ResidualEligible t → RepresentsF (t : ℤ) ∨ RepresentsH (t : ℤ))
    (M : QuaternaryExtension T) (hM : M.PosDef) (h21 : M.Represents 21) :
    M.FibonacciUniversal := by
  obtain ⟨hpos, hcoeff⟩ := q_mem_coefficients M hM h21
  intro n
  by_cases h8 : n = 8
  · subst h8
    rw [show Nat.fib 8 = 21 by decide]
    exact_mod_cast h21
  by_cases hsmall : n < 48
  · obtain ⟨x, y, z, h⟩ := representsF_fib_initial hclass n hsmall h8
    exact M.represents_of_ternary ⟨x, y, z, by rw [fGram_eval]; exact h⟩
  · obtain ⟨x, y, z, k, h⟩ := representsFPlus_fib_of_forty_eight_le hclass hcoeff n (by omega)
    have hq : ((M.q.toNat : ℕ) : ℤ) = M.q := Int.toNat_of_nonneg hpos.le
    rw [hq] at h
    apply represents_of_sub det_pos (k := k)
    exact ⟨x, y, z, by rw [fGram_eval]; linear_combination h⟩

end EscalatorF

end FibonacciCriterion
