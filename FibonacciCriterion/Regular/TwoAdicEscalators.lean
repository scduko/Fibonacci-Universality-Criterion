import FibonacciCriterion.Forms.QuaternaryExtension
import FibonacciCriterion.Regular.TwoAdicSubtraction
import FibonacciCriterion.ClassicalInputs.Representation
import FibonacciCriterion.ClassicalInputs.ThreeSquares.DiagonalReductions
import FibonacciCriterion.ClassicalInputs.ThreeSquares.Scaling
import FibonacciCriterion.Arithmetic.PrimePowerNormalization

/-!
# Ternaries with obstructions at 2 (Lemmas 5.2 and 5.4)

Each of the six ternaries with obstructions at 2 omits one of the families
`E_{ε,r} = {N > 0 : v₂(N) ≡ ε (mod 2), u₂(N) ≡ r (mod 8)}`
(`TwoAdicExceptional ε r`):

| `T` | `(ε, r)` | truant |
| --- | --- | --- |
| `⟨1,1,1⟩`, `⟨1,2,2⟩`, `g` | `(0, 7)` | `F₁₀ = 55` |
| `⟨1,1,2⟩`, `⟨1,2,4⟩` | `(1, 7)` | `F₄₂` |
| `⟨1,2,3⟩` | `(1, 5)` | `F₃₀` |

This file proves the parts of §5.1 that hold for all six escalators:

* the 2-adic rows of Proposition 3.2 in the form
  `T.Represents N ↔ N ∉ E_{ε,r}` (`represents111_iff`, …, `represents123_iff`);
* Lemma 5.2 (`sub_of_high` for (i), `exists_sub_escape` for (ii));
* Lemma 3.6 for these families: `E_{ε,r}` is closed under multiplication by
  nonzero squares (`exceptional_sq_mul`);
* Lemma 5.4 (`not_represents_of_high`);
* Lemma 5.2 (ii) with Lemma 4.1 (iii): `M` represents an exception `N` with
  `v₂(q) ≤ v₂(N) + 2` and `N ≥ 2^{max(4, v₂ N)} q` (`represents_of_low`).
-/

namespace FibonacciCriterion

namespace TwoAdic

open RegularReductions TernaryGram QuaternaryExtension ClassicalRepresentation

/-! ### Lemma 5.2 -/

/-- Lemma 5.2 (i): if `2^{a+3} ∣ q`, subtracting `q k²` from `2^a u` keeps
the valuation and the odd part modulo 8. -/
theorem sub_of_high (a : ℕ) (u q k : ℤ) (hq : 2 ^ (a + 3) ∣ q) :
    ∃ u' : ℤ, 2 ^ a * u - q * k ^ 2 = 2 ^ a * u' ∧ u' % 8 = u % 8 := by
  obtain ⟨t, rfl⟩ := hq
  refine ⟨u - 8 * (t * k ^ 2), by rw [pow_add]; ring, ?_⟩
  generalize t * k ^ 2 = s
  omega

/-- Lemma 5.2 (i), second part: if `2^a u ∈ E_{ε,r}` and `2^{a+3} ∣ q`, every
positive difference `2^a u - q k²` lies in `E_{ε,r}`. -/
theorem exceptional_sub_of_high {ε : ℕ} {r : ℤ} (a : ℕ) (u q k : ℤ)
    (hu : u % 2 = 1) (hexc : a % 2 = ε % 2 ∧ u % 8 = r % 8)
    (hq : 2 ^ (a + 3) ∣ q) (hpos : 0 < 2 ^ a * u - q * k ^ 2) :
    TwoAdicExceptional ε r (2 ^ a * u - q * k ^ 2) := by
  obtain ⟨u', hu', hmod⟩ := sub_of_high a u q k hq
  exact ⟨hpos, a, u', hu', by omega, hexc.1, by omega⟩

/-- Lemma 5.2 (ii): if `v₂(q) ≤ v₂(N) + 2` and `N ≥ 2^{max(4, v₂ N)} q`, some
`k ≥ 1` makes `N - q k²` nonnegative and outside `E_{ε,r}`. -/
theorem exists_sub_escape {ε a s : ℕ} {r : ℤ} (N q u ω : ℤ)
    (hN : N = 2 ^ a * u) (hq : q = 2 ^ s * ω) (hu : u % 2 = 1)
    (hω : ω % 2 = 1) (hexc : a % 2 = ε % 2 ∧ u % 8 = r % 8)
    (hq0 : 0 < q) (hs : s ≤ a + 2) (hroom : 2 ^ max 4 a * q ≤ N) :
    ∃ k : ℤ, 1 ≤ k ∧ 0 ≤ N - q * k ^ 2 ∧
      ¬ TwoAdicExceptional ε r (N - q * k ^ 2) := by
  -- Each choice below has `k² ≤ 2^{max(4, a)}`.
  suffices h : ∃ k : ℤ, 1 ≤ k ∧ k ^ 2 ≤ 2 ^ max 4 a ∧
      ¬ TwoAdicExceptional ε r (N - q * k ^ 2) by
    obtain ⟨k, hk1, hk, hesc⟩ := h
    exact ⟨k, hk1, by nlinarith, hesc⟩
  have h16 : (16 : ℤ) ≤ 2 ^ max 4 a := by
    calc (16 : ℤ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ max 4 a := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  have ha : (2 : ℤ) ^ a ≤ 2 ^ max 4 a :=
    pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
  by_cases hnear : s = a + 2 ∨ s = a + 1 ∨ s = a ∨ a = s + 1 ∨ a = s + 2
  · obtain ⟨k, hk1, hk16, hesc⟩ :=
      twoAdic_subtraction_near ε a s r N q u ω hN hq hu hω hexc.1 hexc.2 hnear
    exact ⟨k, hk1, hk16.trans h16, hesc⟩
  · -- `a - s ≥ 3`.
    obtain ⟨j, hj⟩ : ∃ j, a = s + 3 + j := ⟨a - s - 3, by omega⟩
    rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
    · -- `a - s` odd: `k = 1`.
      refine ⟨1, le_rfl, by simpa using (show (1 : ℤ) ≤ 2 ^ max 4 a from
        le_trans (by norm_num) h16), ?_⟩
      have hN' : N = 2 ^ (s + (2 * t + 3)) * u := by
        rw [hN, hj, ht]
        ring_nf
      simpa using twoAdic_subtraction_far_odd ε s t r N q u ω hN' hq hω
        (by rw [← hexc.1, hj, ht]; ring_nf)
    · -- `a - s` even: `k = 1` or `k = 2^{(a-s-2)/2}`.
      have hN' : N = 2 ^ (s + (2 * t + 4)) * u := by
        rw [hN, hj, ht]
        ring_nf
      obtain ⟨k, hk, hesc⟩ :=
        twoAdic_subtraction_far_even ε s t r N q u ω hN' hq hu hω
      refine ⟨k, ?_, ?_, hesc⟩
      · rcases hk with rfl | rfl
        · exact le_rfl
        · exact one_le_pow₀ (by norm_num)
      · rcases hk with rfl | rfl
        · exact le_trans (by norm_num) h16
        · refine le_trans ?_ ha
          rw [← pow_mul]
          exact pow_le_pow_right₀ (by norm_num) (by omega)

/-! ### Lemma 3.6 for the 2-adic families -/

/-- An odd square is 1 modulo 8. -/
theorem odd_sq_emod_eight {ω : ℤ} (h : ω % 2 = 1) : ω ^ 2 % 8 = 1 := by
  rcases (by omega : ω % 8 = 1 ∨ ω % 8 = 3 ∨ ω % 8 = 5 ∨ ω % 8 = 7) with
    h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

/-- The families `E_{ε,r}` are closed under multiplication by nonzero
squares. -/
theorem exceptional_sq_mul {ε : ℕ} {r N : ℤ} (h : TwoAdicExceptional ε r N)
    (k : ℤ) (hk : k ≠ 0) : TwoAdicExceptional ε r (k ^ 2 * N) := by
  obtain ⟨hN, a, u, rfl, hu, ha, hr⟩ := h
  obtain ⟨s, ω, rfl, hω⟩ := exists_pow_mul_not_dvd 2 (by norm_num) k hk
  have hω2 : ω % 2 = 1 := by
    have : ¬ (2 : ℤ) ∣ ω := by exact_mod_cast hω
    omega
  have hω8 := odd_sq_emod_eight hω2
  refine ⟨by positivity, 2 * s + a, ω ^ 2 * u, ?_, ?_, ?_, ?_⟩
  · push_cast
    rw [pow_add, mul_comm 2 s, pow_mul]
    ring
  · rw [Int.mul_emod, show ω ^ 2 % 2 = 1 by omega, hu]
    norm_num
  · omega
  · rw [Int.mul_emod, hω8]
    simpa using hr

/-! ### The 2-adic rows of Proposition 3.2 -/

/-- For `N ≥ 0`, `N = 4^a (8b + 7)` exactly when `N ∈ E_{0,7}` (Lemma 2.4). The
next two theorems identify `4^a (16b + 14)` with `E_{1,7}` and
`4^a (16b + 10)` with `E_{1,5}`. -/
theorem threeSquareExceptional_iff {N : ℤ} (hN : 0 ≤ N) :
    ThreeSquareExceptional N ↔ TwoAdicExceptional 0 7 N := by
  constructor
  · rintro ⟨a, b, rfl⟩
    have h8 : 0 < 8 * b + 7 := by
      have h0 := (mul_nonneg_iff_of_pos_left (show (0 : ℤ) < 4 ^ a by positivity)).1 hN
      omega
    refine ⟨by positivity, 2 * a, 8 * b + 7, ?_, by omega, by omega, by omega⟩
    rw [pow_mul]
    norm_num
  · rintro ⟨-, a, u, rfl, hu, ha, hr⟩
    obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b := ⟨a / 2, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, u = 8 * c + 7 := ⟨u / 8, by omega⟩
    refine ⟨b, c, ?_⟩
    rw [pow_mul]
    norm_num

theorem exceptional112_iff {N : ℤ} (hN : 0 ≤ N) :
    Exceptional112 N ↔ TwoAdicExceptional 1 7 N := by
  constructor
  · rintro ⟨a, b, rfl⟩
    have h8 : 0 < 16 * b + 14 := by
      have h0 := (mul_nonneg_iff_of_pos_left (show (0 : ℤ) < 4 ^ a by positivity)).1 hN
      omega
    refine ⟨by positivity, 2 * a + 1, 8 * b + 7, ?_, by omega, by omega, by omega⟩
    rw [pow_succ, pow_mul]
    norm_num
    ring
  · rintro ⟨-, a, u, rfl, hu, ha, hr⟩
    obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b + 1 := ⟨a / 2, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, u = 8 * c + 7 := ⟨u / 8, by omega⟩
    refine ⟨b, c, ?_⟩
    rw [pow_succ, pow_mul]
    norm_num
    ring

theorem exceptional123_iff {N : ℤ} (hN : 0 ≤ N) :
    Exceptional123 N ↔ TwoAdicExceptional 1 5 N := by
  constructor
  · rintro ⟨a, b, rfl⟩
    have h8 : 0 < 16 * b + 10 := by
      have h0 := (mul_nonneg_iff_of_pos_left (show (0 : ℤ) < 4 ^ a by positivity)).1 hN
      omega
    refine ⟨by positivity, 2 * a + 1, 8 * b + 5, ?_, by omega, by omega, by omega⟩
    rw [pow_succ, pow_mul]
    norm_num
    ring
  · rintro ⟨-, a, u, rfl, hu, ha, hr⟩
    obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b + 1 := ⟨a / 2, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, u = 8 * c + 5 := ⟨u / 8, by omega⟩
    refine ⟨b, c, ?_⟩
    rw [pow_succ, pow_mul]
    norm_num
    ring

/-- The escalator `g`, with Gram matrix `[[1,0,0],[0,2,1],[0,1,5]]`. -/
abbrev gGram : TernaryGram := ⟨1, 2, 5, 0, 0, 1⟩

/-- Proposition 3.2 for `⟨1,1,1⟩`: a nonnegative integer is represented
exactly when it lies outside `E_{0,7}`. The next five theorems give the
criteria for `⟨1,2,2⟩` and `g` (`E_{0,7}`), `⟨1,1,2⟩` and `⟨1,2,4⟩`
(`E_{1,7}`), and `⟨1,2,3⟩` (`E_{1,5}`). -/
theorem represents111_iff (i : ClassicalInputs) {N : ℤ} (hN : 0 ≤ N) :
    (diag 1 1 1).Represents N ↔ ¬ TwoAdicExceptional 0 7 N := by
  rw [← threeSquareExceptional_iff hN, ← Inputs.threeSquares_criterion i N hN]
  simp [TernaryGram.Represents, ThreeSquares]

theorem represents122_iff (i : ClassicalInputs) {N : ℤ} (hN : 0 ≤ N) :
    (diag 1 2 2).Represents N ↔ ¬ TwoAdicExceptional 0 7 N := by
  rw [← threeSquareExceptional_iff hN, ← Inputs.threeSquares_criterion i N hN,
    ← represents122_iff_threeSquares]
  simp [TernaryGram.Represents, Represents122]

theorem representsG_iff (i : ClassicalInputs) {N : ℤ} (hN : 0 ≤ N) :
    gGram.Represents N ↔ ¬ TwoAdicExceptional 0 7 N := by
  rw [← threeSquareExceptional_iff hN, ← Inputs.threeSquares_criterion i N hN,
    ← Inputs.representsG_iff_threeSquares]
  simp only [TernaryGram.Represents, RepresentsG, TernaryGram.eval]
  constructor <;> rintro ⟨x, y, z, h⟩ <;> exact ⟨x, y, z, by linarith⟩

theorem represents112_iff (i : ClassicalInputs) {N : ℤ} (hN : 0 ≤ N) :
    (diag 1 1 2).Represents N ↔ ¬ TwoAdicExceptional 1 7 N := by
  rw [← exceptional112_iff hN, ← Inputs.represents112_iff_not_exceptional i N hN]
  simp [TernaryGram.Represents, Represents112]

theorem represents124_iff (i : ClassicalInputs) {N : ℤ} (hN : 0 ≤ N) :
    (diag 1 2 4).Represents N ↔ ¬ TwoAdicExceptional 1 7 N := by
  rw [← exceptional112_iff hN, ← Inputs.represents112_iff_not_exceptional i N hN,
    ← represents124_iff_represents112]
  simp [TernaryGram.Represents, Represents124]

theorem represents123_iff (i : ClassicalInputs) {N : ℤ} (hN : 0 ≤ N) :
    (diag 1 2 3).Represents N ↔ ¬ TwoAdicExceptional 1 5 N := by
  rw [← exceptional123_iff hN, ← Inputs.regular123_criterion i N hN]
  simp [TernaryGram.Represents, Represents123]

/-- The necessity direction of a criterion `T.Represents N ↔ N ∉ E_{ε,r}`:
every value of `T` lies outside `E_{ε,r}`. -/
theorem crit_necessity {T : TernaryGram} {ε : ℕ} {r : ℤ} (hT : T.PosDef)
    (hiff : ∀ N : ℤ, 0 ≤ N → (T.Represents N ↔ ¬ TwoAdicExceptional ε r N))
    (N : ℤ) (h : T.Represents N) : ¬ TwoAdicExceptional ε r N := by
  have hN : 0 ≤ N := by
    obtain ⟨x, y, z, rfl⟩ := h
    exact hT.eval_nonneg x y z
  exact (hiff N hN).1 h

/-- The sufficiency direction of a criterion `T.Represents N ↔ N ∉ E_{ε,r}`:
every `N ≥ 0` is a value of `T` or lies in `E_{ε,r}`. -/
theorem crit_dichotomy {T : TernaryGram} {ε : ℕ} {r : ℤ}
    (hiff : ∀ N : ℤ, 0 ≤ N → (T.Represents N ↔ ¬ TwoAdicExceptional ε r N))
    (N : ℤ) (hN : 0 ≤ N) : T.Represents N ∨ TwoAdicExceptional ε r N := by
  by_cases h : TwoAdicExceptional ε r N
  · exact Or.inr h
  · exact Or.inl ((hiff N hN).2 h)

/-! ### Lemma 5.4 and exceptions with `v₂(q) ≤ v₂(N) + 2` -/

/-- Lemma 5.4: if `M` has odd index `d` and `v₂(q) ≥ v₂(τ) + 3`, then `M` does
not represent the exceptional value `τ = 2^v u`. The proof applies the
identity (2) of Lemma 4.1 (ii) (`scaled_eval`) directly; the manuscript cites
its consequence (3). -/
theorem not_represents_of_high {T : TernaryGram} {ε : ℕ} {r : ℤ}
    (hcrit : ∀ N : ℤ, T.Represents N → ¬ TwoAdicExceptional ε r N)
    (hD : 0 < T.det) (hT : T.PosDef) (M : QuaternaryExtension T)
    (hodd : M.index % 2 = 1) (v : ℕ) (u : ℤ) (hu : u % 2 = 1)
    (hexc : v % 2 = ε % 2 ∧ u % 8 = r % 8) (hhigh : 2 ^ (v + 3) ∣ M.q) :
    ¬ M.Represents (2 ^ v * u) := by
  rintro ⟨x, y, z, w, hxyzw⟩
  have hs := scaled_eval (M := M) hD x y z w
  rw [hxyzw] at hs
  set X := T.eval (M.index * x + w * M.β₁) (M.index * y + w * M.β₂)
    (M.index * z + w * M.β₃)
  have hX : 0 ≤ X := hT.eval_nonneg _ _ _
  -- `d² τ = 2^v (d² u)` with `d² u ≡ u (mod 8)`.
  have hd8 := odd_sq_emod_eight hodd
  obtain ⟨u', hu', hmod⟩ := sub_of_high v (M.index ^ 2 * u) M.q w hhigh
  have hdu : (M.index ^ 2 * u) % 8 = u % 8 := by
    rw [Int.mul_emod, hd8]
    simp
  have hXeq : X = 2 ^ v * u' := by linear_combination hu' - hs
  have hu'odd : u' % 2 = 1 := by omega
  have hXpos : 0 < X := by
    rcases hX.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hXeq
      rcases mul_eq_zero.1 hXeq.symm with h0 | h0
      · exact pow_ne_zero _ (by norm_num) h0
      · omega
  exact hcrit X ⟨_, _, _, rfl⟩
    ⟨hXpos, v, u', hXeq, hu'odd, hexc.1, by omega⟩

/-- Lemma 5.2 (ii) with Lemma 4.1 (iii), the step used in Proposition 5.1 when
`v₂(q) ≤ v₂(N) + 2`: `M` represents an exceptional `N = 2^a u` once
`N ≥ 2^{max(4, a)} q`. -/
theorem represents_of_low {T : TernaryGram} {ε : ℕ} {r : ℤ}
    (hcrit : ∀ N : ℤ, 0 ≤ N → ¬ TwoAdicExceptional ε r N → T.Represents N)
    (hD : 0 < T.det) (M : QuaternaryExtension T) (hM : M.PosDef) (a : ℕ)
    (u : ℤ) (hu : u % 2 = 1) (hexc : a % 2 = ε % 2 ∧ u % 8 = r % 8)
    (hlow : ¬ 2 ^ (a + 3) ∣ M.q) (hroom : 2 ^ max 4 a * M.q ≤ 2 ^ a * u) :
    M.Represents (2 ^ a * u) := by
  have hq0 := q_pos hD hM
  obtain ⟨s, ω, hq, hω, hs⟩ := exists_twoAdic_normalization_lt M.q hq0 (a + 3)
    (fun h => hlow (Int.dvd_of_emod_eq_zero h))
  obtain ⟨k, -, hk0, hesc⟩ :=
    exists_sub_escape (ε := ε) (r := r) (2 ^ a * u) M.q u ω rfl hq hu hω hexc
      hq0 (by omega) hroom
  exact represents_of_sub hD (hcrit _ hk0 hesc)

end TwoAdic

end FibonacciCriterion
