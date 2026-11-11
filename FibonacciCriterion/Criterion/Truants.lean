import FibonacciCriterion.Criterion.FourSquareExtension

/-!
# Fibonacci truants are indispensable (§7)

If a form `P` omits a Fibonacci number `t` and represents every smaller one,
the four-square extension of `P` represents every Fibonacci number except `t`
(`exists_fibonacci_omission`), so every Fibonacci criterion set contains `t`
(`criterion_contains_truant`). Apart from Lagrange's four-square theorem (in
`Criterion.FourSquareExtension`), no representation theorem is used; the
criteria of Proposition 3.2 enter only in `Criterion.Indispensability`, which
applies this to the escalators `P_t` of Table 1.
-/

namespace FibonacciCriterion

variable {ι : Type} [Fintype ι]

/-- If `P` omits `t` and represents every Fibonacci number below `t`, its
four-square extension represents every Fibonacci number other than `t` and
omits `t`. The rank of the extension stays symbolic. -/
theorem exists_fibonacci_omission
    (P : Form ι) (t : ℕ) (hmiss : ¬ P.Represents t)
    (hlower : ∀ n : ℕ, Nat.fib n < t → P.Represents (Nat.fib n)) :
    ∃ V : Form (ι ⊕ (Fin 4 ⊕ Fin (t + 1))),
      (¬ V.Represents t) ∧
      (∀ n : ℕ, Nat.fib n ≠ t → V.Represents (Nat.fib n)) := by
  obtain ⟨V, hVmiss, hVparent, hVabove⟩ := exists_form_extension P t hmiss
  refine ⟨V, hVmiss, ?_⟩
  intro n hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact hVparent (Nat.fib n) (hlower n hlt)
  · exact hVabove (Nat.fib n) hgt

/-- If `t` is the Fibonacci truant of a form `P`, that is, `P` omits the
Fibonacci number `t` and represents every smaller one, then every set of
Fibonacci numbers with the forcing property `IsFibonacciCriterion` contains
`t`. -/
theorem criterion_contains_truant
    (S : Set ℕ)
    (hS : ∀ s ∈ S, ∃ n : ℕ, Nat.fib n = s)
    (hcriterion : IsFibonacciCriterion S)
    (P : Form ι) (t : ℕ)
    (ht : ∃ n : ℕ, Nat.fib n = t)
    (hmiss : ¬ P.Represents t)
    (hlower : ∀ n : ℕ, Nat.fib n < t → P.Represents (Nat.fib n)) :
    t ∈ S := by
  by_contra hnot
  obtain ⟨V, hVmiss, hVother⟩ := exists_fibonacci_omission P t hmiss hlower
  have hVS : ∀ s ∈ S, V.Represents s := by
    intro s hs
    obtain ⟨n, hn⟩ := hS s hs
    have hne : Nat.fib n ≠ t := by
      intro heq
      apply hnot
      have hst : s = t := hn.symm.trans heq
      simpa [hst] using hs
    simpa [hn] using hVother n hne
  obtain ⟨n, hn⟩ := ht
  have hVall := hcriterion (ι ⊕ (Fin 4 ⊕ Fin (t + 1))) V hVS
  apply hVmiss
  simpa [hn] using hVall n

end FibonacciCriterion
