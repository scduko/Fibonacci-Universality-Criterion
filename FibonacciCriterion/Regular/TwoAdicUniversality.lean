import FibonacciCriterion.Regular.TwoAdicExtensions

/-!
# Fibonacci-universality in the 2-adic cases (Proposition 5.1)

Every positive-definite quaternary extension of one of the six ternaries with
obstructions at 2 that represents its truant is Fibonacci-universal
(`fibonacciUniversal_111`, `_122`, `_g`, `_112`, `_124`, `_123`).

As in the manuscript, an extension with `v₂(q) ≤ v₂(τ) + 2` is handled by
Lemmas 4.1, 5.2, and 5.3, with Lemma 5.5 for `F₂₂` when `T = g`. By
Proposition 5.7, an extension with `v₂(q) ≥ v₂(τ) + 3` is one of the fourteen
extensions of `⟨1,2,2⟩` listed there; the other five ternaries have none.
-/

namespace FibonacciCriterion

namespace TwoAdic

open RegularReductions TernaryGram QuaternaryExtension ClassicalRepresentation

/-! ### Proposition 5.1 -/

/-- Proposition 5.1 for `⟨1,1,1⟩`: every positive-definite extension
representing 55 is Fibonacci-universal (`q̄_T = 55`). -/
theorem fibonacciUniversal_111 (i : FibonacciClassicalInputs)
    (M : QuaternaryExtension (diag 1 1 1)) (hM : M.PosDef) (h55 : M.Represents 55) :
    M.FibonacciUniversal := by
  have hiff := fun N (hN : (0 : ℤ) ≤ N) => represents111_iff i.representation hN
  have hq := q_le_det_sq_mul (by norm_num) hM h55 (not_represents_truant_111 i.representation)
  have hq0 := (q_pos (by norm_num) hM).le
  norm_num at hq
  apply fibonacciUniversal_of_room (fun N hN h => (hiff N hN).2 h) (by norm_num) M hM 0
    (by simpa using not_high_111 i.representation M h55) h55
  intro n hT' h
  exact Or.inr (room_even_seven i.valuations (crit_dichotomy hiff) n hT' h M.q hq0
    (by omega) (fun _ => by omega))

/-- Proposition 5.1 for `⟨1,2,2⟩`: every positive-definite extension
representing 55 is Fibonacci-universal (`q̄_T = 880`). Up to a change of
generator, those with `v₂(q) ≥ 3` are the fourteen extensions of
Proposition 5.7. -/
theorem fibonacciUniversal_122 (i : FibonacciClassicalInputs)
    (M : QuaternaryExtension (diag 1 2 2)) (hM : M.PosDef) (h55 : M.Represents 55) :
    M.FibonacciUniversal := by
  have hiff := fun N (hN : (0 : ℤ) ≤ N) => represents122_iff i.representation hN
  by_cases h8 : 8 ∣ M.q
  · obtain ⟨a₁, a₂, a₃, m, hshift, hm, hm3, hm55⟩ :=
      high_122 i.representation M hM h55 h8
    rw [← fibonacciUniversal_shift_iff M a₁ a₂ a₃, hshift]
    exact (extension122_universal i hm hm3 hm55).2.2.2.2
  have hq := q_le_det_sq_mul (by norm_num) hM h55 (not_represents_truant_122 i.representation)
  have hq0 := (q_pos (by norm_num) hM).le
  norm_num at hq
  apply fibonacciUniversal_of_room (fun N hN h => (hiff N hN).2 h) (by norm_num) M hM 0
    (by simpa using h8) h55
  intro n hT' h
  exact Or.inr (room_even_seven i.valuations (crit_dichotomy hiff) n hT' h M.q hq0
    (by omega) (fun _ => by omega))

/-- Proposition 5.1 for `g`: every positive-definite extension representing
55 is Fibonacci-universal (`q̄_T = 4455`), with Lemma 5.5 for `F₂₂`. -/
theorem fibonacciUniversal_g (i : FibonacciClassicalInputs)
    (M : QuaternaryExtension gGram) (hM : M.PosDef) (h55 : M.Represents 55) :
    M.FibonacciUniversal := by
  have hD : 0 < gGram.det := by rw [det_g]; norm_num
  have hiff := fun N (hN : (0 : ℤ) ≤ N) => representsG_iff i.representation hN
  have hq := q_le_det_sq_mul hD hM h55 (not_represents_truant_g i.representation)
  have hq0 := (q_pos hD hM).le
  rw [det_g] at hq
  norm_num at hq
  apply fibonacciUniversal_of_room (fun N hN h => (hiff N hN).2 h) hD M hM 0
    (by simpa using not_high_g i.representation M h55) h55
  intro n hT' h
  by_cases h22 : n = 22
  · subst h22
    exact Or.inl (fib22 ▸ g_represents_F22 i.representation M hM h55)
  · exact Or.inr (room_even_seven i.valuations (crit_dichotomy hiff) n hT' h M.q hq0
      (by omega) (fun h' => absurd h' h22))

/-- Proposition 5.1 for `⟨1,1,2⟩`: every positive-definite extension
representing `F₄₂` is Fibonacci-universal (`q̄_T = 4 F₄₂`). -/
theorem fibonacciUniversal_112 (i : FibonacciClassicalInputs)
    (M : QuaternaryExtension (diag 1 1 2)) (hM : M.PosDef)
    (hτ : M.Represents 267914296) : M.FibonacciUniversal := by
  have hiff := fun N (hN : (0 : ℤ) ≤ N) => represents112_iff i.representation hN
  have hq := q_le_det_sq_mul (by norm_num) hM hτ (not_represents_truant_112 i.representation)
  have hq0 := (q_pos (by norm_num) hM).le
  norm_num at hq
  apply fibonacciUniversal_of_room (fun N hN h => (hiff N hN).2 h) (by norm_num) M hM 3
    (by simpa using not_high_112 i.representation M hτ) hτ
  intro n hT' h
  exact Or.inr (room_odd_seven i.valuations (crit_dichotomy hiff) n hT' h M.q hq0 (by omega))

/-- Proposition 5.1 for `⟨1,2,4⟩`: every positive-definite extension
representing `F₄₂` is Fibonacci-universal (`q̄_T = 64 F₄₂`), with Lemma 5.6
for `v₂(q) ≥ 6`. -/
theorem fibonacciUniversal_124 (i : FibonacciClassicalInputs)
    (M : QuaternaryExtension (diag 1 2 4)) (hM : M.PosDef)
    (hτ : M.Represents 267914296) : M.FibonacciUniversal := by
  have hiff := fun N (hN : (0 : ℤ) ≤ N) => represents124_iff i.representation hN
  have hq := q_le_det_sq_mul (by norm_num) hM hτ (not_represents_truant_124 i.representation)
  have hq0 := (q_pos (by norm_num) hM).le
  norm_num at hq
  apply fibonacciUniversal_of_room (fun N hN h => (hiff N hN).2 h) (by norm_num) M hM 3
    (by simpa using not_high_124 i.representation M hτ) hτ
  intro n hT' h
  exact Or.inr (room_odd_seven i.valuations (crit_dichotomy hiff) n hT' h M.q hq0 (by omega))

/-- Proposition 5.1 for `⟨1,2,3⟩`: every positive-definite extension
representing `F₃₀` is Fibonacci-universal (`q̄_T = 36 F₃₀`). -/
theorem fibonacciUniversal_123 (i : FibonacciClassicalInputs)
    (M : QuaternaryExtension (diag 1 2 3)) (hM : M.PosDef)
    (hτ : M.Represents 832040) : M.FibonacciUniversal := by
  have hiff := fun N (hN : (0 : ℤ) ≤ N) => represents123_iff i.representation hN
  have hq := q_le_det_sq_mul (by norm_num) hM hτ (not_represents_truant_123 i.representation)
  have hq0 := (q_pos (by norm_num) hM).le
  norm_num at hq
  apply fibonacciUniversal_of_room (fun N hN h => (hiff N hN).2 h) (by norm_num) M hM 3
    (by simpa using not_high_123 i.representation M hτ) hτ
  intro n hT' h
  exact Or.inr (room_odd_five i.valuations (crit_dichotomy hiff) n hT' h M.q hq0 (by omega))

end TwoAdic

end FibonacciCriterion
