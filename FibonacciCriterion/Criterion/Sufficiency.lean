import FibonacciCriterion.Statement
import FibonacciCriterion.Escalation.NineTernaryFrames
import FibonacciCriterion.Escalation.TernaryTruants
import FibonacciCriterion.Escalation.QuaternaryEscalation
import FibonacciCriterion.Regular.TwoAdicUniversality

/-!
# Sufficiency of the criterion (§7)

Let `Q` be a form that represents every element of `criterion`. The escalation
of Proposition 3.1 (`exists_nine_ternary_frame`) finds vectors of `Q` with the
Gram matrix of one of the nine ternary escalators `T`. Together with a vector
`u` of `Q` whose norm is the truant `τ` of `T`, they span the quaternary
extension `T + ℤu`, which has rank 4 by Lemma 3.6 and represents `τ`. By
Propositions 5.1, 5.11, 5.12, and 6.1 this extension is Fibonacci-universal,
and so is `Q` (`criterionSufficiency_of_classical`).
-/

namespace FibonacciCriterion

open TernaryGram

/-- The truant of each of the nine ternary escalators belongs to `criterion`. -/
theorem escalatorTruant_mem {b d e : ℤ} (hp : NineTernaryEscalator b d e) :
    escalatorTruant b d e ∈ criterion := by
  rw [← fib_criterionIndices]
  apply Finset.mem_image_of_mem
  rcases hp with ⟨rfl, rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl, rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl, rfl | rfl⟩ <;> decide

/-- Each of the nine ternary escalators `T` is positive definite and omits
every nonzero square multiple of its truant (Lemma 3.6), and every positive-definite
quaternary extension of `T` that represents the truant is
Fibonacci-universal (Propositions 5.1, 5.11, 5.12, and 6.1). -/
theorem escalator_extensions (i : FibonacciClassicalInputs) {b d e : ℤ}
    (hp : NineTernaryEscalator b d e) :
    (escalatorGram b d e).PosDef ∧
      (∀ k : ℤ, k ≠ 0 →
        ¬ (escalatorGram b d e).Represents (k ^ 2 * escalatorTruant b d e)) ∧
      ∀ M : QuaternaryExtension (escalatorGram b d e), M.PosDef →
        M.Represents (escalatorTruant b d e) → M.FibonacciUniversal := by
  have hdiag : ∀ {B C : ℤ}, 0 < B → 0 < C → (diag 1 B C).PosDef :=
    fun hB hC => diag_posDef (by norm_num) hB hC
  rcases hp with ⟨rfl, rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl, rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl, rfl | rfl⟩ <;> simp only [escalatorTruant, escalatorTruantIndex] <;>
    norm_num
  · -- `⟨1,1,1⟩`
    exact ⟨hdiag (by norm_num) (by norm_num),
      fun k hk => by exact_mod_cast TwoAdic.not_represents_sq_mul_111 i.representation k hk,
      fun M hM h => TwoAdic.fibonacciUniversal_111 i M hM (by exact_mod_cast h)⟩
  · -- `⟨1,1,2⟩`
    exact ⟨hdiag (by norm_num) (by norm_num),
      fun k hk => by exact_mod_cast TwoAdic.not_represents_sq_mul_112 i.representation k hk,
      fun M hM h => TwoAdic.fibonacciUniversal_112 i M hM (by exact_mod_cast h)⟩
  · -- `⟨1,1,3⟩`
    exact ⟨Escalator113.posDef,
      fun k hk => by exact_mod_cast
        Escalator113.not_represents_sq_mul_truant i.representation k hk,
      fun M hM h => Escalator113.fibonacciUniversal i M hM (by exact_mod_cast h)⟩
  · -- `⟨1,2,2⟩`
    exact ⟨hdiag (by norm_num) (by norm_num),
      fun k hk => by exact_mod_cast TwoAdic.not_represents_sq_mul_122 i.representation k hk,
      fun M hM h => TwoAdic.fibonacciUniversal_122 i M hM (by exact_mod_cast h)⟩
  · -- `⟨1,2,3⟩`
    exact ⟨hdiag (by norm_num) (by norm_num),
      fun k hk => by exact_mod_cast TwoAdic.not_represents_sq_mul_123 i.representation k hk,
      fun M hM h => TwoAdic.fibonacciUniversal_123 i M hM (by exact_mod_cast h)⟩
  · -- `⟨1,2,4⟩`
    exact ⟨hdiag (by norm_num) (by norm_num),
      fun k hk => by exact_mod_cast TwoAdic.not_represents_sq_mul_124 i.representation k hk,
      fun M hM h => TwoAdic.fibonacciUniversal_124 i M hM (by exact_mod_cast h)⟩
  · -- `⟨1,2,5⟩`
    exact ⟨Escalator125.posDef,
      fun k hk => by exact_mod_cast
        Escalator125.not_represents_sq_mul_truant i.representation k hk,
      fun M hM h => Escalator125.fibonacciUniversal i M hM (by exact_mod_cast h)⟩
  · -- `f`
    exact ⟨EscalatorF.posDef,
      fun k hk => by exact_mod_cast EscalatorF.not_represents_sq_mul_truant k hk,
      fun M hM h => EscalatorF.fibonacciUniversal
        (ClassicalRepresentation.Inputs.eligible_f_or_h i.representation) M hM
        (by exact_mod_cast h)⟩
  · -- `g`
    exact ⟨TwoAdic.posDef_g,
      fun k hk => by exact_mod_cast TwoAdic.not_represents_sq_mul_g i.representation k hk,
      fun M hM h => TwoAdic.fibonacciUniversal_g i M hM (by exact_mod_cast h)⟩

/-- Given the classical results, a positive-definite form of any finite rank
that represents every element of `criterion` is Fibonacci-universal (part of
Theorem 1.1). -/
theorem criterionSufficiency_of_classical (i : FibonacciClassicalInputs) :
    CriterionSufficiency := by
  intro ι _ Q hcriterion
  obtain ⟨b, d, e, v, u, r, hp, hv, hu, hr, huv, hrv, hru⟩ :=
    Q.exists_nine_ternary_frame (hcriterion 1 (by decide)) (hcriterion 2 (by decide))
      (hcriterion 3 (by decide)) (hcriterion 5 (by decide))
  have hf : Q.IsFrame (escalatorGram b d e) v u r :=
    ⟨hv, hu, hr, (Q.pairing_comm _ _).trans huv, (Q.pairing_comm _ _).trans hrv,
      (Q.pairing_comm _ _).trans hru⟩
  obtain ⟨hT, homit, hclose⟩ := escalator_extensions i hp
  exact Q.fibonacciUniversal_of_frame hf hT homit hclose
    (hcriterion _ (escalatorTruant_mem hp))

end FibonacciCriterion
