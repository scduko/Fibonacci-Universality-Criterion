import FibonacciCriterion.Regular.TwoAdicEscalators
import FibonacciCriterion.Regular.TwoAdicFibonacci
import FibonacciCriterion.ClassicalInputs.Definitions

/-!
# Extensions of the ternaries with obstructions at 2 (§5.1)

For each of the six ternaries `T` with obstructions at 2, with truant `τ`, this
file proves:

* Lemma 3.6: `T` omits every nonzero square multiple of `τ`
  (`not_represents_sq_mul_111`, …), in particular `τ`
  (`not_represents_truant_111`, …);
* the case `v₂(q) ≤ v₂(τ) + 2` of Proposition 5.1
  (`fibonacciUniversal_of_room`), with the size bounds of Lemma 5.3 for the
  three families (`room_even_seven`, `room_odd_seven`, `room_odd_five`); in
  these names, `room` is the size hypothesis `N ≥ 2^{max(4, v₂ N)} q` of
  Lemma 5.2 (ii);
* the representatives of §4.1 for `g` (`exists_rep_g`);
* the exclusions of Proposition 5.7: no extension of `⟨1,1,1⟩`, `g`,
  `⟨1,1,2⟩`, `⟨1,2,3⟩` representing `τ` has `v₂(q) ≥ v₂(τ) + 3`, by Lemma 5.4
  or because `v₂(q) = 1` (`not_high_111`, …), and Lemma 5.6 for `⟨1,2,4⟩`
  (`not_high_124`);
* Proposition 5.7 for `⟨1,2,2⟩`: after a change of generator, the extensions
  representing 55 with `v₂(q) ≥ 3` are exactly the fourteen extensions
  `c = (0, 1, 1)`, `m ≡ 3 (mod 4)`, `3 ≤ m ≤ 55` (`high_122`), and they are
  Fibonacci-universal (`extension122_universal`);
* Lemma 5.5: every extension of `g` representing 55 represents `F₂₂`
  (`g_represents_F22`).
-/

namespace FibonacciCriterion

namespace TwoAdic

open RegularReductions TernaryGram QuaternaryExtension ClassicalRepresentation

/-! ### The truants and the form `g` -/

theorem fib10 : (Nat.fib 10 : ℤ) = 55 := by norm_num [Nat.fib_add_two]

theorem fib22 : (Nat.fib 22 : ℤ) = 17711 := by norm_num [Nat.fib_add_two]

theorem fib30 : (Nat.fib 30 : ℤ) = 832040 := by norm_num [Nat.fib_add_two]

theorem fib42 : (Nat.fib 42 : ℤ) = 267914296 := by norm_num [Nat.fib_add_two]

/-- `F₄₂ = 267914296 = 2³ · 33489287`; the odd part is `7 (mod 8)`. -/
theorem truantF42 : (267914296 : ℤ) = 2 ^ 3 * 33489287 := by norm_num

/-- `F₃₀ = 832040 = 2³ · 104005`; the odd part is `5 (mod 8)`. -/
theorem truantF30 : (832040 : ℤ) = 2 ^ 3 * 104005 := by norm_num

/-- `g` is positive definite: `g = x² + y² + 4z² + (y + z)²`. -/
theorem posDef_g : gGram.PosDef := by
  intro x y z h
  have hd := diag_posDef (a := 1) (b := 1) (c := 4) (by norm_num) (by norm_num)
    (by norm_num) x y z h
  rw [diag_eval] at hd
  have e : gGram.eval x y z = 1 * x ^ 2 + 1 * y ^ 2 + 4 * z ^ 2 + (y + z) ^ 2 := by
    simp only [TernaryGram.eval]
    ring
  rw [e]
  linarith [sq_nonneg (y + z)]

/-! ### Lemma 3.6 -/

/-- Lemma 3.6 for a 2-adic family: if `T` represents exactly the nonnegative
integers outside `E_{ε,r}`, it omits every nonzero square multiple of a member
of `E_{ε,r}`. -/
theorem not_represents_sq_mul_of_exceptional {T : TernaryGram} {ε : ℕ} {r : ℤ}
    (hT : T.PosDef)
    (hiff : ∀ N : ℤ, 0 ≤ N → (T.Represents N ↔ ¬ TwoAdicExceptional ε r N))
    {τ : ℤ} (hτ : TwoAdicExceptional ε r τ) (k : ℤ) (hk : k ≠ 0) :
    ¬ T.Represents (k ^ 2 * τ) :=
  fun h => crit_necessity hT hiff _ h (exceptional_sq_mul hτ k hk)

/-- Lemma 2.4 for the truants: 55, `F₄₂ = 2³ · 33489287`, and
`F₃₀ = 2³ · 104005` belong to `E_{0,7}`, `E_{1,7}`, and `E_{1,5}` (this theorem
and the next two). -/
theorem exceptional55 : TwoAdicExceptional 0 7 55 :=
  ⟨by norm_num, 0, 55, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem exceptionalF42 : TwoAdicExceptional 1 7 267914296 :=
  ⟨by norm_num, 3, 33489287, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem exceptionalF30 : TwoAdicExceptional 1 5 832040 :=
  ⟨by norm_num, 3, 104005, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Lemma 3.6 for `⟨1,1,1⟩`: it omits every nonzero square multiple of its
truant 55. The next five theorems state the same for `⟨1,2,2⟩`, `g`,
`⟨1,1,2⟩`, `⟨1,2,4⟩`, and `⟨1,2,3⟩`. -/
theorem not_represents_sq_mul_111 (i : ClassicalInputs) (k : ℤ) (hk : k ≠ 0) :
    ¬ (diag 1 1 1).Represents (k ^ 2 * 55) :=
  not_represents_sq_mul_of_exceptional (diag_posDef (by norm_num) (by norm_num)
    (by norm_num)) (fun _ hN => represents111_iff i hN) exceptional55 k hk

theorem not_represents_sq_mul_122 (i : ClassicalInputs) (k : ℤ) (hk : k ≠ 0) :
    ¬ (diag 1 2 2).Represents (k ^ 2 * 55) :=
  not_represents_sq_mul_of_exceptional (diag_posDef (by norm_num) (by norm_num)
    (by norm_num)) (fun _ hN => represents122_iff i hN) exceptional55 k hk

theorem not_represents_sq_mul_g (i : ClassicalInputs) (k : ℤ) (hk : k ≠ 0) :
    ¬ gGram.Represents (k ^ 2 * 55) :=
  not_represents_sq_mul_of_exceptional posDef_g (fun _ hN => representsG_iff i hN)
    exceptional55 k hk

theorem not_represents_sq_mul_112 (i : ClassicalInputs) (k : ℤ) (hk : k ≠ 0) :
    ¬ (diag 1 1 2).Represents (k ^ 2 * 267914296) :=
  not_represents_sq_mul_of_exceptional (diag_posDef (by norm_num) (by norm_num)
    (by norm_num)) (fun _ hN => represents112_iff i hN) exceptionalF42 k hk

theorem not_represents_sq_mul_124 (i : ClassicalInputs) (k : ℤ) (hk : k ≠ 0) :
    ¬ (diag 1 2 4).Represents (k ^ 2 * 267914296) :=
  not_represents_sq_mul_of_exceptional (diag_posDef (by norm_num) (by norm_num)
    (by norm_num)) (fun _ hN => represents124_iff i hN) exceptionalF42 k hk

theorem not_represents_sq_mul_123 (i : ClassicalInputs) (k : ℤ) (hk : k ≠ 0) :
    ¬ (diag 1 2 3).Represents (k ^ 2 * 832040) :=
  not_represents_sq_mul_of_exceptional (diag_posDef (by norm_num) (by norm_num)
    (by norm_num)) (fun _ hN => represents123_iff i hN) exceptionalF30 k hk

/-- Lemma 3.6 with `k = 1`: `⟨1,1,1⟩` omits its truant 55. The next five
theorems state the same for the other five ternaries with obstructions at 2. -/
theorem not_represents_truant_111 (i : ClassicalInputs) : ¬ (diag 1 1 1).Represents 55 := by
  simpa using not_represents_sq_mul_111 i 1 one_ne_zero

theorem not_represents_truant_122 (i : ClassicalInputs) : ¬ (diag 1 2 2).Represents 55 := by
  simpa using not_represents_sq_mul_122 i 1 one_ne_zero

theorem not_represents_truant_g (i : ClassicalInputs) : ¬ gGram.Represents 55 := by
  simpa using not_represents_sq_mul_g i 1 one_ne_zero

theorem not_represents_truant_112 (i : ClassicalInputs) :
    ¬ (diag 1 1 2).Represents 267914296 := by
  simpa using not_represents_sq_mul_112 i 1 one_ne_zero

theorem not_represents_truant_124 (i : ClassicalInputs) :
    ¬ (diag 1 2 4).Represents 267914296 := by
  simpa using not_represents_sq_mul_124 i 1 one_ne_zero

theorem not_represents_truant_123 (i : ClassicalInputs) :
    ¬ (diag 1 2 3).Represents 832040 := by
  simpa using not_represents_sq_mul_123 i 1 one_ne_zero

/-! ### The case `v₂(q) ≤ v₂(τ) + 2` of Proposition 5.1 -/

/-- Proposition 5.1 when `v₂(q) ≤ v + 2`: suppose that `M` represents `τ`, and
that every Fibonacci number other than `τ` omitted by `T` is either
represented by `M` or an element `2^a u` of `E_{ε,r}` with `a ≥ v` and
`2^{max(4, a)} q ≤ 2^a u`. Then Lemmas 4.1 and 5.2 make `M`
Fibonacci-universal. The six theorems of `Regular.TwoAdicUniversality` take
`v = v₂(τ)` (0 for 55, 3 for `F₄₂` and `F₃₀`); `extension122_universal` takes
`v = 4`, since the even exceptions of `⟨1,2,2⟩` have valuation at least 4. -/
theorem fibonacciUniversal_of_room {T : TernaryGram} {ε : ℕ} {r : ℤ}
    (hcrit : ∀ N : ℤ, 0 ≤ N → ¬ TwoAdicExceptional ε r N → T.Represents N)
    (hD : 0 < T.det) (M : QuaternaryExtension T) (hM : M.PosDef) (v : ℕ)
    (hlow : ¬ 2 ^ (v + 3) ∣ M.q) {τ : ℤ} (hτ : M.Represents τ)
    (hroom : ∀ n : ℕ, ¬ T.Represents (Nat.fib n) → (Nat.fib n : ℤ) ≠ τ →
      M.Represents (Nat.fib n) ∨ ∃ (a : ℕ) (u : ℤ),
        (Nat.fib n : ℤ) = 2 ^ a * u ∧ u % 2 = 1 ∧ a % 2 = ε % 2 ∧
          u % 8 = r % 8 ∧ v ≤ a ∧ 2 ^ max 4 a * M.q ≤ Nat.fib n) :
    M.FibonacciUniversal := by
  intro n
  by_cases hT : T.Represents (Nat.fib n)
  · exact M.represents_of_ternary hT
  by_cases hn : (Nat.fib n : ℤ) = τ
  · exact hn ▸ hτ
  rcases hroom n hT hn with h | ⟨a, u, hfac, hu, ha, hr, hva, hroom⟩
  · exact h
  rw [hfac]
  refine represents_of_low hcrit hD M hM a u hu ⟨ha, hr⟩ ?_ (hfac ▸ hroom)
  intro hdvd
  exact hlow ((pow_dvd_pow 2 (by omega)).trans hdvd)

/-- Lemma 5.3 for `E_{0,7}`: suppose that every nonnegative integer omitted by
`T` lies in `E_{0,7}`. If `T` omits `Fₙ ≠ 55`, then `Fₙ = 2^a u` lies in
`E_{0,7}` and `2^{max(4, a)} q ≤ Fₙ` for every `q` with `0 ≤ q ≤ 4455`, where
`q ≤ 880` is required when `n = 22`. -/
theorem room_even_seven (iv : FibonacciValuationInputs) {T : TernaryGram}
    (hrep : ∀ N : ℤ, 0 ≤ N → T.Represents N ∨ TwoAdicExceptional 0 7 N)
    (n : ℕ) (hT : ¬ T.Represents (Nat.fib n)) (h55 : (Nat.fib n : ℤ) ≠ 55)
    (q : ℤ) (hq0 : 0 ≤ q) (hq : q ≤ 4455) (h22 : n = 22 → q ≤ 880) :
    ∃ (a : ℕ) (u : ℤ), (Nat.fib n : ℤ) = 2 ^ a * u ∧ u % 2 = 1 ∧
      a % 2 = 0 % 2 ∧ u % 8 = 7 % 8 ∧ 0 ≤ a ∧ 2 ^ max 4 a * q ≤ Nat.fib n := by
  have hex := (hrep _ (by positivity)).resolve_left hT
  obtain ⟨-, a, u, hfac, hu, ha, hr⟩ := id hex
  refine ⟨a, u, hfac, hu, ha, hr, Nat.zero_le _, ?_⟩
  exact TwoAdicFibonacci.size_bound_even_seven iv n a u hfac hu hex
    (by rintro rfl; exact h55 fib10) q hq0 hq h22

/-- Lemma 5.3 for `E_{1,7}`: suppose that every nonnegative integer omitted by
`T` lies in `E_{1,7}`. If `T` omits `Fₙ ≠ F₄₂`, then `Fₙ = 2^a u` lies in
`E_{1,7}`, `a ≥ 3` (`three_le_of_odd`), and `2^{max(4, a)} q ≤ Fₙ` for every
`q` with `0 ≤ q ≤ 64 F₄₂`. -/
theorem room_odd_seven (iv : FibonacciValuationInputs) {T : TernaryGram}
    (hrep : ∀ N : ℤ, 0 ≤ N → T.Represents N ∨ TwoAdicExceptional 1 7 N)
    (n : ℕ) (hT : ¬ T.Represents (Nat.fib n))
    (hτ : (Nat.fib n : ℤ) ≠ 267914296) (q : ℤ) (hq0 : 0 ≤ q)
    (hq : q ≤ 64 * 267914296) :
    ∃ (a : ℕ) (u : ℤ), (Nat.fib n : ℤ) = 2 ^ a * u ∧ u % 2 = 1 ∧
      a % 2 = 1 % 2 ∧ u % 8 = 7 % 8 ∧ 3 ≤ a ∧ 2 ^ max 4 a * q ≤ Nat.fib n := by
  have hex := (hrep _ (by positivity)).resolve_left hT
  obtain ⟨-, a, u, hfac, hu, ha, hr⟩ := id hex
  refine ⟨a, u, hfac, hu, ha, hr,
    TwoAdicFibonacci.three_le_of_odd n a u (Or.inl rfl) hfac (by omega) hr, ?_⟩
  exact TwoAdicFibonacci.size_bound_odd iv n a u hfac hu
    (Or.inl ⟨hex, by rintro rfl; exact hτ fib42⟩) q hq0 hq

/-- Lemma 5.3 for `E_{1,5}`: suppose that every nonnegative integer omitted by
`T` lies in `E_{1,5}`. If `T` omits `Fₙ ≠ F₃₀`, then `Fₙ = 2^a u` lies in
`E_{1,5}`, `a ≥ 3` (`three_le_of_odd`), and `2^{max(4, a)} q ≤ Fₙ` for every
`q` with `0 ≤ q ≤ 64 F₄₂`. -/
theorem room_odd_five (iv : FibonacciValuationInputs) {T : TernaryGram}
    (hrep : ∀ N : ℤ, 0 ≤ N → T.Represents N ∨ TwoAdicExceptional 1 5 N)
    (n : ℕ) (hT : ¬ T.Represents (Nat.fib n))
    (hτ : (Nat.fib n : ℤ) ≠ 832040) (q : ℤ) (hq0 : 0 ≤ q)
    (hq : q ≤ 64 * 267914296) :
    ∃ (a : ℕ) (u : ℤ), (Nat.fib n : ℤ) = 2 ^ a * u ∧ u % 2 = 1 ∧
      a % 2 = 1 % 2 ∧ u % 8 = 5 % 8 ∧ 3 ≤ a ∧ 2 ^ max 4 a * q ≤ Nat.fib n := by
  have hex := (hrep _ (by positivity)).resolve_left hT
  obtain ⟨-, a, u, hfac, hu, ha, hr⟩ := id hex
  refine ⟨a, u, hfac, hu, ha, hr,
    TwoAdicFibonacci.three_le_of_odd n a u (Or.inr rfl) hfac (by omega) hr, ?_⟩
  exact TwoAdicFibonacci.size_bound_odd iv n a u hfac hu
    (Or.inr ⟨hex, by rintro rfl; exact hτ fib30⟩) q hq0 hq

/-! ### Representatives (§4.1) -/

/-- The representatives of §4.1 for `g`: after a change of generator,
`c = (0, 0, c₃)` with `0 ≤ c₃ ≤ 8`. -/
theorem exists_rep_g (M : QuaternaryExtension gGram) :
    ∃ a₁ a₂ a₃ : ℤ, (M.shift a₁ a₂ a₃).c₁ = 0 ∧
      (M.shift a₁ a₂ a₃).c₂ = 0 ∧ 0 ≤ (M.shift a₁ a₂ a₃).c₃ ∧
      (M.shift a₁ a₂ a₃).c₃ < 9 := by
  set a₂ := (M.c₃ - 5 * M.c₂) / 9
  refine ⟨-M.c₁, a₂, -M.c₂ - 2 * a₂, ?_, ?_, ?_, ?_⟩ <;>
    simp only [shift, TernaryGram.mul₁, TernaryGram.mul₂, TernaryGram.mul₃] <;>
    omega

/-! ### Proposition 5.7: the exclusions -/

/-- Proposition 5.7 for `⟨1,1,1⟩`: no extension representing 55 has
`v₂(q) ≥ 3`. The representative is `c = 0`, so the index is 1 and Lemma 5.4
applies. -/
theorem not_high_111 (i : ClassicalInputs) (M : QuaternaryExtension (diag 1 1 1))
    (h55 : M.Represents 55) : ¬ 8 ∣ M.q := by
  intro h8
  have hcrit := crit_necessity (diag_posDef (by norm_num) (by norm_num) (by norm_num))
    (fun N hN => represents111_iff i hN)
  obtain ⟨a₁, a₂, a₃, h1, h2, h2', h3, h3'⟩ :=
    exists_shift_diag (B := 1) (C := 1) (by norm_num) (by norm_num) 0 0 M
  rw [← q_shift (by norm_num) M a₁ a₂ a₃] at h8
  have h55' := (represents_shift_iff M a₁ a₂ a₃).2 h55
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h2' h3 h3' h8 h55'
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h2' h3 h3'
  obtain rfl : c₂ = 0 := by omega
  obtain rfl : c₃ = 0 := by omega
  subst h1
  exact not_represents_of_high hcrit (by norm_num)
    (diag_posDef (by norm_num) (by norm_num) (by norm_num)) _
    (by quaternary_norm) 0 55 (by norm_num) (by norm_num) h8 (by simpa using h55')

theorem det_g : gGram.det = 9 := by decide

/-- Proposition 5.7 for `g`: no extension representing 55 has `v₂(q) ≥ 3`.
The index divides 9, so it is odd, and Lemma 5.4 applies. -/
theorem not_high_g (i : ClassicalInputs) (M : QuaternaryExtension gGram)
    (h55 : M.Represents 55) : ¬ 8 ∣ M.q := by
  intro h8
  have hcrit := crit_necessity posDef_g (fun N hN => representsG_iff i hN)
  obtain ⟨a₁, a₂, a₃, h1, h2, h3, h3'⟩ := exists_rep_g M
  rw [← q_shift (by rw [det_g]; norm_num) M a₁ a₂ a₃] at h8
  have h55' := (represents_shift_iff M a₁ a₂ a₃).2 h55
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h3 h3' h8 h55'
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h3 h3'
  subst h1 h2
  refine not_represents_of_high hcrit (by rw [det_g]; norm_num) posDef_g _ ?_ 0 55
    (by norm_num) (by norm_num) h8 (by simpa using h55')
  interval_cases c₃ <;> quaternary_norm

/-- Proposition 5.7 for `⟨1,1,2⟩`: no extension representing `F₄₂` has
`v₂(q) ≥ 6`. With `c = (0, 0, 1)`, `q = 4 m - 2`; with `c = 0`, the index is 1
and Lemma 5.4 applies. -/
theorem not_high_112 (i : ClassicalInputs) (M : QuaternaryExtension (diag 1 1 2))
    (hτ : M.Represents 267914296) : ¬ 64 ∣ M.q := by
  intro h64
  have hT := diag_posDef (a := 1) (b := 1) (c := 2) (by norm_num) (by norm_num)
    (by norm_num)
  have hcrit := crit_necessity hT (fun N hN => represents112_iff i hN)
  obtain ⟨a₁, a₂, a₃, h1, h2, h2', h3, h3'⟩ :=
    exists_shift_diag (B := 1) (C := 2) (by norm_num) (by norm_num) 0 0 M
  rw [← q_shift (by norm_num) M a₁ a₂ a₃] at h64
  have hτ' := (represents_shift_iff M a₁ a₂ a₃).2 hτ
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h2' h3 h3' h64 hτ'
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h2' h3 h3'
  obtain rfl : c₂ = 0 := by omega
  subst h1
  rcases (by omega : c₃ = 0 ∨ c₃ = 1) with rfl | rfl
  · exact not_represents_of_high hcrit (by norm_num) hT _ (by quaternary_norm) 3
      33489287 (by norm_num) (by norm_num) h64 (by rw [← truantF42]; exact hτ')
  · revert h64
    quaternary_norm
    omega

/-- Proposition 5.7 for `⟨1,2,3⟩`: no extension representing `F₃₀` has
`v₂(q) ≥ 6`. With `c₂ = 1`, `v₂(q) = 1`; with `c₂ = 0`, the index is 1 or 3
and Lemma 5.4 applies. -/
theorem not_high_123 (i : ClassicalInputs) (M : QuaternaryExtension (diag 1 2 3))
    (hτ : M.Represents 832040) : ¬ 64 ∣ M.q := by
  intro h64
  have hT := diag_posDef (a := 1) (b := 2) (c := 3) (by norm_num) (by norm_num)
    (by norm_num)
  have hcrit := crit_necessity hT (fun N hN => represents123_iff i hN)
  obtain ⟨a₁, a₂, a₃, h1, h2, h2', h3, h3'⟩ :=
    exists_shift_diag (B := 2) (C := 3) (by norm_num) (by norm_num) 0 0 M
  rw [← q_shift (by norm_num) M a₁ a₂ a₃] at h64
  have hτ' := (represents_shift_iff M a₁ a₂ a₃).2 hτ
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h2' h3 h3' h64 hτ'
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h2' h3 h3'
  subst h1
  rcases (by omega : c₂ = 0 ∨ c₂ = 1) with rfl | rfl
  · refine not_represents_of_high hcrit (by norm_num) hT _ ?_ 3 104005
      (by norm_num) (by norm_num) h64 (by rw [← truantF30]; exact hτ')
    interval_cases c₃ <;> quaternary_norm
  · revert h64
    interval_cases c₃ <;> quaternary_norm <;> omega

/-- `x² + 2y²` is never 7 or 15 modulo 16. -/
theorem sq_add_two_sq_mod_sixteen (x y : ZMod 16) :
    x ^ 2 + 2 * y ^ 2 ≠ 7 ∧ x ^ 2 + 2 * y ^ 2 ≠ 15 := by
  revert x y
  decide

theorem odd_sq_mod_sixteen (x : ZMod 16) (hx : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7 ∨
    x = 9 ∨ x = 11 ∨ x = 13 ∨ x = 15) : x ^ 2 = 1 ∨ x ^ 2 = 9 := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Lemma 5.6: no extension of `⟨1,2,4⟩` representing its truant `F₄₂` has
`v₂(q) ≥ 6`. -/
theorem not_high_124 (i : ClassicalInputs) (M : QuaternaryExtension (diag 1 2 4))
    (hτ : M.Represents 267914296) : ¬ 64 ∣ M.q := by
  intro h64
  have hT := diag_posDef (a := 1) (b := 2) (c := 4) (by norm_num) (by norm_num)
    (by norm_num)
  have hcrit := crit_necessity hT (fun N hN => represents124_iff i hN)
  obtain ⟨a₁, a₂, a₃, h1, h2, h2', h3, h3'⟩ :=
    exists_shift_diag (B := 2) (C := 4) (by norm_num) (by norm_num) 0 0 M
  rw [← q_shift (by norm_num) M a₁ a₂ a₃] at h64
  have hτ' := (represents_shift_iff M a₁ a₂ a₃).2 hτ
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h2' h3 h3' h64 hτ'
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h2' h3 h3'
  subst h1
  rcases (by omega : c₂ = 0 ∨ c₂ = 1) with rfl | rfl <;>
    rcases (by omega : c₃ = 0 ∨ c₃ = 1 ∨ c₃ = 2 ∨ c₃ = 3) with rfl | rfl | rfl | rfl
  · -- `c = 0`: Lemma 5.4.
    exact not_represents_of_high hcrit (by norm_num) hT _ (by quaternary_norm) 3
      33489287 (by norm_num) (by norm_num) h64 (by rw [← truantF42]; exact hτ')
  · revert h64; quaternary_norm; omega
  · -- `c = (0, 0, 2)`: `q = 4 (m - 1)` and the parity argument.
    have hq : (⟨0, 0, 2, m⟩ : QuaternaryExtension (diag 1 2 4)).q = 4 * (m - 1) := by
      quaternary_norm; ring
    rw [hq] at h64
    obtain ⟨x, y, z, w, hxyzw⟩ := hτ'
    simp only [QuaternaryExtension.eval, diag_eval] at hxyzw
    rcases Int.even_or_odd w with ⟨w', rfl⟩ | ⟨w', rfl⟩
    · -- `w = 2 w'`: `F₄₂ - 4 (m - 1) w'²` is a value of `⟨1,2,4⟩` in `E_{1,7}`.
      apply hcrit (2 ^ 3 * 33489287 - 4 * (m - 1) * w' ^ 2) ⟨x, y, z + w', by
        rw [diag_eval]; linear_combination hxyzw⟩
      apply exceptional_sub_of_high 3 33489287 (4 * (m - 1)) w' (by norm_num)
        (by norm_num) (by simpa using h64)
      have := hT.eval_nonneg x y (z + w')
      rw [diag_eval] at this
      obtain ⟨u', hu', hmod⟩ := sub_of_high 3 33489287 (4 * (m - 1)) w'
        (by simpa using h64)
      rcases this.lt_or_eq with h | h
      · linarith
      · exfalso
        have h0 : (2 : ℤ) ^ 3 * u' = 0 := by linarith
        omega
    · -- `w` odd: residues modulo 16.
      have h16 : (16 : ℤ) ∣ m - 1 := by omega
      obtain ⟨t, ht⟩ := h16
      have hz := congrArg (fun n : ℤ => (n : ZMod 16)) hxyzw
      push_cast at hz
      have hm : ((m : ℤ) : ZMod 16) = 1 := by
        have : m = 16 * t + 1 := by omega
        rw [this]
        push_cast
        rw [show (16 : ZMod 16) = 0 from rfl]
        ring
      rw [hm] at hz
      have hw : ((2 * w' + 1 : ℤ) : ZMod 16) = (2 * (w' : ZMod 16) + 1) := by push_cast; ring
      have hodd := odd_sq_mod_sixteen (2 * (z : ZMod 16) + (2 * (w' : ZMod 16) + 1))
        (by generalize (z : ZMod 16) = a; generalize (w' : ZMod 16) = b; revert a b; decide)
      have hF : ((267914296 : ℤ) : ZMod 16) = 8 := by decide
      obtain ⟨h7, h15⟩ := sq_add_two_sq_mod_sixteen (x : ZMod 16) (y : ZMod 16)
      have key : (x : ZMod 16) ^ 2 + 2 * (y : ZMod 16) ^ 2 =
          8 - (2 * (z : ZMod 16) + (2 * (w' : ZMod 16) + 1)) ^ 2 := by
        rw [← hF]
        push_cast
        linear_combination hz
      rcases hodd with h | h <;> rw [h] at key
      · exact h7 (by rw [key]; decide)
      · exact h15 (by rw [key]; decide)
  · revert h64; quaternary_norm; omega
  · revert h64; quaternary_norm; omega
  · revert h64; quaternary_norm; omega
  · revert h64; quaternary_norm; omega
  · revert h64; quaternary_norm; omega

/-! ### Proposition 5.7 for `⟨1,2,2⟩`: the fourteen extensions -/

/-- The extension of `⟨1,2,2⟩` with `c = (0, 1, 1)` and norm `m`. -/
abbrev extension122 (m : ℤ) : QuaternaryExtension (diag 1 2 2) := ⟨0, 1, 1, m⟩

theorem extension122_q (m : ℤ) : (extension122 m).q = 4 * (m - 1) := by
  quaternary_norm
  ring

/-- `2 Q = 2x² + (2y + w)² + (2z + w)² + 2 (m - 1) w²`. -/
theorem extension122_eval (m x y z w : ℤ) :
    2 * (extension122 m).eval x y z w =
      2 * x ^ 2 + (2 * y + w) ^ 2 + (2 * z + w) ^ 2 + 2 * (m - 1) * w ^ 2 := by
  simp only [QuaternaryExtension.eval, diag_eval]
  ring

theorem extension122_posDef {m : ℤ} (hm : 2 ≤ m) : (extension122 m).PosDef := by
  intro x y z w h
  have e := extension122_eval m x y z w
  have h2 : 0 < 2 * (extension122 m).eval x y z w := by
    rw [e]
    by_cases hw : w = 0
    · subst hw
      by_cases hx : x = 0
      · subst hx
        by_cases hy : y = 0
        · have hz : z ≠ 0 := fun hz => h ⟨rfl, hy, hz, rfl⟩
          have := pow_pos (abs_pos.2 hz) 2
          rw [sq_abs] at this
          nlinarith
        · have := pow_pos (abs_pos.2 hy) 2
          rw [sq_abs] at this
          nlinarith [sq_nonneg (2 * z)]
      · have := pow_pos (abs_pos.2 hx) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg (2 * y), sq_nonneg (2 * z)]
    · have := pow_pos (abs_pos.2 hw) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg x, sq_nonneg (2 * y + w), sq_nonneg (2 * z + w)]
  linarith

/-- For `m ≡ 3 (mod 4)` and `m ≤ 55`, this extension represents every
`N ≥ 55` with `N ≡ 7 (mod 8)`: at `w = 1` its value is
`x² + (y + z + 1)² + (y - z)² + m - 1`. -/
theorem extension122_represents_seven (i : ClassicalInputs) {m : ℤ} (hm : m % 4 = 3)
    (hm55 : m ≤ 55) {N : ℤ} (hN : 55 ≤ N) (h7 : N % 8 = 7) :
    (extension122 m).Represents N := by
  -- `N - (m - 1)` is `1` or `5 (mod 8)`, hence a sum of three squares.
  have hR : 0 ≤ N - (m - 1) := by omega
  obtain ⟨a, b, c, habc⟩ := (represents111_iff i hR).2 (by
    apply not_twoAdicExceptional_of_normalization 0 0 7 _ (N - (m - 1)) (by omega)
      (by simp)
    right
    omega)
  simp only [diag_eval, one_mul] at habc
  -- Exactly one of `a, b, c` is odd; write `N - (m - 1) = X² + Y² + 4 Z²`.
  have hsq : ∀ t : ℤ, t ^ 2 % 4 = t % 2 := by
    intro t
    rcases Int.even_or_odd t with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega
  have h4 : (a ^ 2 + b ^ 2 + c ^ 2) % 4 = 1 := by rw [habc]; omega
  obtain ⟨X, Y, Z, hXY, hXYZ⟩ : ∃ X Y Z : ℤ, (X + Y) % 2 = 1 ∧
      X ^ 2 + Y ^ 2 + 4 * Z ^ 2 = N - (m - 1) := by
    have ha := hsq a
    have hb := hsq b
    have hc := hsq c
    rcases Int.even_or_odd c with ⟨k, rfl⟩ | hc'
    · refine ⟨a, b, k, by omega, by linear_combination habc⟩
    · rcases Int.even_or_odd b with ⟨k, rfl⟩ | hb'
      · refine ⟨a, c, k, by omega, by linear_combination habc⟩
      · obtain ⟨k, rfl⟩ : Even a := by
          rcases Int.even_or_odd a with h | ⟨k, rfl⟩
          · exact h
          · exfalso
            obtain ⟨j, rfl⟩ := hb'
            obtain ⟨l, rfl⟩ := hc'
            omega
        refine ⟨b, c, k, by omega, by linear_combination habc⟩
  refine ⟨2 * Z, (X + Y - 1) / 2, (X - Y - 1) / 2, 1, ?_⟩
  have hy : 2 * ((X + Y - 1) / 2) = X + Y - 1 := by omega
  have hz : 2 * ((X - Y - 1) / 2) = X - Y - 1 := by omega
  have := extension122_eval m (2 * Z) ((X + Y - 1) / 2) ((X - Y - 1) / 2) 1
  rw [hy, hz] at this
  linarith

/-- Proposition 5.7 for `⟨1,2,2⟩`, classification: an extension of `⟨1,2,2⟩`
representing 55 with `v₂(q) ≥ 3` is, after a change of generator, one of the
fourteen extensions `c = (0, 1, 1)`, `m ≡ 3 (mod 4)`, `3 ≤ m ≤ 55`. -/
theorem high_122 (i : ClassicalInputs) (M : QuaternaryExtension (diag 1 2 2))
    (hM : M.PosDef) (h55 : M.Represents 55) (h8 : 8 ∣ M.q) :
    ∃ (a₁ a₂ a₃ m : ℤ), M.shift a₁ a₂ a₃ = extension122 m ∧ m % 4 = 3 ∧
      3 ≤ m ∧ m ≤ 55 := by
  have hT := diag_posDef (a := 1) (b := 2) (c := 2) (by norm_num) (by norm_num)
    (by norm_num)
  have hcrit := crit_necessity hT (fun N hN => represents122_iff i hN)
  obtain ⟨a₁, a₂, a₃, h1, h2, h2', h3, h3'⟩ :=
    exists_shift_diag (B := 2) (C := 2) (by norm_num) (by norm_num) 0 0 M
  rw [← q_shift (by norm_num) M a₁ a₂ a₃] at h8
  have h55' := (represents_shift_iff M a₁ a₂ a₃).2 h55
  have hM' := hM.shift a₁ a₂ a₃
  refine ⟨a₁, a₂, a₃, ?_⟩
  generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h2' h3 h3' h8 h55' hM' ⊢
  obtain ⟨c₁, c₂, c₃, m⟩ := M'
  simp only at h1 h2 h2' h3 h3'
  subst h1
  have hT55 := not_represents_truant_122 i
  rcases (by omega : c₂ = 0 ∨ c₂ = 1) with rfl | rfl <;>
    rcases (by omega : c₃ = 0 ∨ c₃ = 1) with rfl | rfl
  · exact absurd (by simpa using h55') (not_represents_of_high hcrit (by norm_num) hT _
      (by quaternary_norm) 0 55 (by norm_num) (by norm_num) h8)
  · revert h8; quaternary_norm; omega
  · revert h8; quaternary_norm; omega
  · -- `c = (0, 1, 1)`: `q = 4 (m - 1)`, `δ = m - 1 ≤ 55`.
    refine ⟨m, rfl, ?_⟩
    have hq := extension122_q m
    have hm := det_mul_m_le (by norm_num) hM' h55' hT55
    have hpos := q_pos (by norm_num) hM'
    have hcα : (extension122 m).cα = 4 := by quaternary_norm
    rw [hcα] at hm
    rw [hq] at hpos h8
    norm_num at hm
    have hm3 : m % 4 = 3 := by
      -- `m ≡ 1 (mod 4)` would omit 55, by the parity of `w`.
      by_contra hm1
      have hm1 : m % 4 = 1 := by omega
      obtain ⟨x, y, z, w, hxyzw⟩ := h55'
      simp only [QuaternaryExtension.eval, diag_eval] at hxyzw
      rcases Int.even_or_odd w with ⟨r, rfl⟩ | ⟨s, rfl⟩
      · -- `w = 2r`: `Q = x² + 2(y + r)² + 2(z + r)² + 4(m - 1) r²`, and
        -- `55 - 4(m - 1) r²` would be a value of `⟨1,2,2⟩` in `E_{0,7}`.
        have hrep : (diag 1 2 2).Represents (2 ^ 0 * 55 - 4 * (m - 1) * r ^ 2) :=
          ⟨x, y + r, z + r, by rw [diag_eval]; linear_combination hxyzw⟩
        have h8' : 2 ^ (0 + 3) ∣ 4 * (m - 1) := ⟨(m - 1) / 2, by omega⟩
        obtain ⟨u', hu', hmod⟩ := sub_of_high 0 55 (4 * (m - 1)) r h8'
        have hpos : 0 < 2 ^ 0 * 55 - 4 * (m - 1) * r ^ 2 := by
          obtain ⟨a, b, c, habc⟩ := hrep
          have := hT.eval_nonneg a b c
          rw [diag_eval] at this habc
          rcases this.lt_or_eq with h | h
          · linarith
          · rw [hu'] at habc
            omega
        exact hcrit _ hrep (exceptional_sub_of_high 0 55 (4 * (m - 1)) r (by norm_num)
          (by norm_num) h8' hpos)
      · -- `w` odd: `Q ≡ x² + m ≡ x² + 1 (mod 4)`, never `55 ≡ 3`.
        obtain ⟨a, ha⟩ : Even (y * (y + (2 * s + 1))) := by
          rcases Int.even_or_odd y with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · exact ⟨k * (k + k + (2 * s + 1)), by ring⟩
          · exact ⟨(2 * k + 1) * (k + s + 1), by ring⟩
        obtain ⟨b, hb⟩ : Even (z * (z + (2 * s + 1))) := by
          rcases Int.even_or_odd z with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · exact ⟨k * (k + k + (2 * s + 1)), by ring⟩
          · exact ⟨(2 * k + 1) * (k + s + 1), by ring⟩
        have hx4 : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
          rcases Int.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · left; ring_nf; omega
          · right; ring_nf; omega
        have hQ : x ^ 2 + 4 * (a + b) + m * (4 * (s ^ 2 + s) + 1) = 55 := by
          linear_combination hxyzw - 2 * ha - 2 * hb
        generalize x ^ 2 = X at hQ hx4
        generalize s ^ 2 + s = t at hQ
        have : m * (4 * t + 1) = 4 * (m * t) + m := by ring
        rw [this] at hQ
        generalize m * t = mt at hQ
        omega
    exact ⟨hm3, by omega, by omega⟩

/-- Proposition 5.7 for `⟨1,2,2⟩`, converse: each of the fourteen extensions
is positive definite, has `v₂(q) = 3`, represents the truant 55, and is
Fibonacci-universal. -/
theorem extension122_universal (i : FibonacciClassicalInputs) {m : ℤ} (hm : m % 4 = 3)
    (hm3 : 3 ≤ m) (hm55 : m ≤ 55) :
    (extension122 m).PosDef ∧ 8 ∣ (extension122 m).q ∧ ¬ 16 ∣ (extension122 m).q ∧
      (extension122 m).Represents 55 ∧ (extension122 m).FibonacciUniversal := by
  have hq := extension122_q m
  have hM := extension122_posDef (m := m) (by omega)
  have h55 : (extension122 m).Represents 55 :=
    extension122_represents_seven i.representation hm hm55 le_rfl (by norm_num)
  refine ⟨hM, by rw [hq]; omega, by rw [hq]; omega, h55, ?_⟩
  -- Odd exceptions by the construction; even ones have valuation at least 4.
  have hiff := fun N (hN : (0 : ℤ) ≤ N) => represents122_iff i.representation hN
  apply fibonacciUniversal_of_room (fun N hN h => (hiff N hN).2 h) (by norm_num) _ hM 4
    (by rw [hq]; omega) h55
  intro n hT hn55
  have hdich := crit_dichotomy hiff
  obtain ⟨a, u, hfac, hu, ha, hr, -, hroom⟩ :=
    room_even_seven i.valuations hdich n hT hn55 (extension122 m).q
      (by rw [hq]; omega) (by rw [hq]; omega) (fun _ => by rw [hq]; omega)
  have hn : 1 ≤ n := by
    by_contra h0
    obtain rfl : n = 0 := by omega
    simp at hfac
    omega
  rcases TwoAdicFibonacci.even_valuation_zero_or_four_le i.valuations n a u hn hfac hu
      (by omega) with rfl | h4
  · -- Odd exception: `Fₙ ≡ 7 (mod 8)` and `Fₙ > 55`.
    left
    have hge : (55 : ℤ) ≤ Nat.fib n := by
      have := hroom
      rw [hq] at this
      simp at this
      nlinarith
    exact extension122_represents_seven i.representation hm hm55 hge
      (by rw [hfac]; simp; omega)
  · exact Or.inr ⟨a, u, hfac, hu, ha, hr, h4, hroom⟩

/-! ### Lemma 5.5 -/

/-- Lemma 5.5: every extension of `g` representing its truant 55 also
represents `F₂₂ = 17711`. -/
theorem g_represents_F22 (i : ClassicalInputs) (M : QuaternaryExtension gGram)
    (hM : M.PosDef) (h55 : M.Represents 55) : M.Represents 17711 := by
  have hD : 0 < gGram.det := by rw [det_g]; norm_num
  have hiff := fun N (hN : (0 : ℤ) ≤ N) => representsG_iff i hN
  have hcrit := crit_necessity posDef_g hiff
  have hT55 := not_represents_truant_g i
  have hnot8 := not_high_g i M h55
  have hq0 := q_pos hD hM
  -- `d ∣ 9`: either `d ≤ 3` and `q ≤ 9 · 55`, or `d = 9` and `q = 81 m - 18 c₃²`.
  have key : M.q ≤ 495 ∨ (M.q ≤ 4455 ∧ 9 ∣ M.q) := by
    obtain ⟨a₁, a₂, a₃, h1, h2, h3, h3'⟩ := exists_rep_g M
    rw [← q_shift hD M a₁ a₂ a₃]
    have h55' := (represents_shift_iff M a₁ a₂ a₃).2 h55
    have hM' := hM.shift a₁ a₂ a₃
    have hb := q_le_index_sq_mul hD hM' h55' hT55
    generalize M.shift a₁ a₂ a₃ = M' at h1 h2 h3 h3' hb
    obtain ⟨c₁, c₂, c₃, m⟩ := M'
    simp only at h1 h2 h3 h3'
    subst h1 h2
    revert hb
    interval_cases c₃ <;> quaternary_norm <;> omega
  have hsuff : ∀ R : ℤ, 0 ≤ R → ¬ TwoAdicExceptional 0 7 R → gGram.Represents R :=
    fun R hR h => (hiff R hR).2 h
  by_cases hq2 : 2 ∣ M.q
  · -- `v₂(q) ∈ {1, 2}`: `F₂₂ - q` is odd and not `7 (mod 8)`.
    apply represents_of_sub hD (k := 1)
    apply hsuff _ (by omega)
    apply not_twoAdicExceptional_of_normalization 0 0 7 _ (17711 - M.q * 1 ^ 2)
      (by omega) (by simp)
    right
    omega
  · by_cases hsmall : 4 * M.q ≤ 17711
    · -- Odd `q ≤ F₂₂ / 4`: `F₂₂ - 4 q ≡ 3 (mod 8)`.
      apply represents_of_sub hD (k := 2)
      apply hsuff _ (by omega)
      apply not_twoAdicExceptional_of_normalization 0 0 7 _ (17711 - M.q * 2 ^ 2)
        (by omega) (by simp)
      right
      omega
    · -- Odd `q > F₂₂ / 4` forces `d = 9` and `q ∈ {4437, 4455}`.
      apply represents_of_sub hD (k := 1)
      apply hsuff _ (by omega)
      rcases (by omega : M.q = 4437 ∨ M.q = 4455) with h | h <;> rw [h]
      · exact not_twoAdicExceptional_of_normalization 0 1 7 _ 6637 (by norm_num)
          (by norm_num) (Or.inl (by norm_num))
      · exact not_twoAdicExceptional_of_normalization 0 3 7 _ 1657 (by norm_num)
          (by norm_num) (Or.inl (by norm_num))

end TwoAdic

end FibonacciCriterion
