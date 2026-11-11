import FibonacciCriterion.Escalation.NineTernaryEscalators
import FibonacciCriterion.Regular.TwoAdicExtensions
import FibonacciCriterion.Regular.Escalator113
import FibonacciCriterion.Regular.Escalator125
import FibonacciCriterion.Irregular.EscalatorF

/-!
# The Fibonacci truants of the nine ternary escalators (Propositions 3.2 and 3.5)

`truant_column` proves the truant column of Figure 1 from the classical
representation theorems: each of the nine ternary escalators `T`, with truant
`τ = Fₖ`, represents every `Fₙ` with `n < k` and omits `τ`. Minimality uses it
for the six ternary escalators of Table 1 (`Criterion.Indispensability`), and
Corollary 1.2 for `⟨1,1,2⟩` (`Criterion.Proof`).

For the regular escalators, representation below the truant combines the
criteria of Proposition 3.2 with Lemma 2.4: no earlier Fibonacci number lies
in the exceptional family. For `f`, the values `F₀, …, F₇` have displayed
representations (`Irregular.representsF_fib_of_lt_eight`), so the proof does
not use the field `eligible_f_or_h` of `ClassicalInputs`, that is,
Proposition 3.3. Omission of the truant
is the case `k = 1` of Lemma 3.6 in its integral form: `T` omits `k² τ` for
every `k ≠ 0`. These facts are proven in `Regular/` and
`Irregular/EscalatorF`, which this file imports.
-/

namespace FibonacciCriterion

open TernaryGram

/-- The index `k` of the Fibonacci truant `Fₖ` of each of the nine ternary
escalators: 10 for `⟨1,1,1⟩`, `⟨1,2,2⟩`, `g`; 42 for `⟨1,1,2⟩`, `⟨1,2,4⟩`; 16
for `⟨1,1,3⟩`; 30 for `⟨1,2,3⟩`; 15 for `⟨1,2,5⟩`; 8 for `f`. -/
def escalatorTruantIndex (b d e : ℤ) : ℕ :=
  if e = 1 then (if d = 4 then 8 else 10)
  else if b = 1 then (if d = 1 then 10 else if d = 2 then 42 else 16)
  else if d = 2 then 10 else if d = 3 then 30 else if d = 4 then 42 else 15

/-- The Fibonacci truant of each of the nine ternary escalators. -/
def escalatorTruant (b d e : ℤ) : ℕ := Nat.fib (escalatorTruantIndex b d e)

/-- Propositions 3.2 and 3.5, truant column of Figure 1: each of the nine
ternary escalators represents every Fibonacci number before its truant and
omits the truant. -/
theorem truant_column (c : ClassicalInputs) {b d e : ℤ} (hp : NineTernaryEscalator b d e) :
    (∀ n : ℕ, n < escalatorTruantIndex b d e →
      (escalatorGram b d e).Represents (Nat.fib n)) ∧
      ¬ (escalatorGram b d e).Represents (escalatorTruant b d e) := by
  -- Representation below the truant from a 2-adic criterion and Lemma 2.4.
  have below {T : TernaryGram} {ε : ℕ} {r : ℤ}
      (hiff : ∀ N : ℤ, 0 ≤ N → (T.Represents N ↔ ¬ TwoAdic.TwoAdicExceptional ε r N))
      {k : ℕ} (hk : ∀ n < k, ¬ TwoAdic.TwoAdicExceptional ε r (Nat.fib n)) :
      ∀ n < k, T.Represents (Nat.fib n) :=
    fun n hn => (hiff _ (by positivity)).2 (hk n hn)
  have seven0 : ∀ n < 10,
      ¬ TwoAdic.TwoAdicExceptional 0 7 (Nat.fib n) := fun n hn hex => by
    rcases TwoAdicFibonacci.member_even_seven n hex with h | h | h <;> omega
  rcases hp with ⟨rfl, rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl, rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl, rfl | rfl⟩ <;> simp only [escalatorTruant, escalatorTruantIndex] <;>
    norm_num
  · -- `⟨1,1,1⟩`
    exact ⟨below (fun _ hN => TwoAdic.represents111_iff c hN) seven0,
      TwoAdic.not_represents_truant_111 c⟩
  · -- `⟨1,1,2⟩`
    exact ⟨below (fun _ hN => TwoAdic.represents112_iff c hN)
        TwoAdicFibonacci.no_odd_seven_exception_below_forty_two,
      TwoAdic.not_represents_truant_112 c⟩
  · -- `⟨1,1,3⟩`
    exact ⟨Escalator113.represents_fib_below_sixteen c,
      Escalator113.not_represents_truant c⟩
  · -- `⟨1,2,2⟩`
    exact ⟨below (fun _ hN => TwoAdic.represents122_iff c hN) seven0,
      TwoAdic.not_represents_truant_122 c⟩
  · -- `⟨1,2,3⟩`
    exact ⟨below (fun _ hN => TwoAdic.represents123_iff c hN)
        TwoAdicFibonacci.no_odd_five_exception_below_thirty,
      TwoAdic.not_represents_truant_123 c⟩
  · -- `⟨1,2,4⟩`
    exact ⟨below (fun _ hN => TwoAdic.represents124_iff c hN)
        TwoAdicFibonacci.no_odd_seven_exception_below_forty_two,
      TwoAdic.not_represents_truant_124 c⟩
  · -- `⟨1,2,5⟩`
    exact ⟨Escalator125.represents_fib_below_fifteen c,
      Escalator125.not_represents_truant c⟩
  · -- `f`: the displayed vectors for `F₀, …, F₇`.
    refine ⟨fun n hn => ?_, by
      simpa [show (Nat.fib 8 : ℤ) = 21 by norm_num [Nat.fib_add_two]] using
        EscalatorF.not_represents_truant⟩
    exact (Irregular.fGram_represents_iff _).2 (Irregular.representsF_fib_of_lt_eight n hn)
  · -- `g`
    exact ⟨below (fun _ hN => TwoAdic.representsG_iff c hN) seven0,
      TwoAdic.not_represents_truant_g c⟩

end FibonacciCriterion
