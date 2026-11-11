import FibonacciCriterion.Irregular.Forms

/-!
# Eligible integers not divisible by 49

Proposition 3.3 calls a positive integer `N` eligible if `v₇(N)` is even or
`u₇(N) ≡ 1, 2, 4 (mod 7)`. For `N` not divisible by 49 this says that `N` is
prime to 7 or that `N / 7` is a nonzero square modulo 7; `ResidualEligible`
states this condition. Every eligible integer is a power of 49 times a
`ResidualEligible` one.
-/

namespace FibonacciCriterion.Irregular

/-- `N` is positive, not divisible by 49, and eligible: either `7 ∤ N` or
`N / 7 ≡ 1, 2, 4 (mod 7)`. The version for integers, modulo 49, is
`Eligibility.EligibleResidue` (`eligibleResidue_iff_residualEligible`). -/
def ResidualEligible (N : ℕ) : Prop :=
  0 < N ∧ N % 49 ≠ 0 ∧
    (N % 7 ≠ 0 ∨ N / 7 % 7 = 1 ∨ N / 7 % 7 = 2 ∨ N / 7 % 7 = 4)

instance (N : ℕ) : Decidable (ResidualEligible N) :=
  inferInstanceAs (Decidable (0 < N ∧ N % 49 ≠ 0 ∧
    (N % 7 ≠ 0 ∨ N / 7 % 7 = 1 ∨ N / 7 % 7 = 2 ∨ N / 7 % 7 = 4)))

end FibonacciCriterion.Irregular
