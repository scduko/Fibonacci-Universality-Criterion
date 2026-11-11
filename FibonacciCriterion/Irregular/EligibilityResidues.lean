import FibonacciCriterion.Irregular.Eligibility

/-!
# Eligibility as a condition modulo 49

`EligibleResidue` is the eligibility condition of Proposition 3.3 for integers
not divisible by 49, written modulo 49; it depends only on the class modulo 49
(`eligibleResidue_of_mod_eq`). The residue class of Lemma 6.3 is `exists_seven_choice`
in `Irregular.Subtraction`.
-/

namespace FibonacciCriterion.Eligibility

/-- The eligibility condition modulo 49: `a` is prime to 7, or
`a ≡ 7, 14, 28 (mod 49)`. Positivity is not included; for a positive integer
this is `Irregular.ResidualEligible`. -/
def EligibleResidue (a : ℤ) : Prop :=
  a % 7 ≠ 0 ∨ a % 49 = 7 ∨ a % 49 = 14 ∨ a % 49 = 28

instance (a : ℤ) : Decidable (EligibleResidue a) := by
  unfold EligibleResidue
  infer_instance

/-- Eligibility depends only on the class modulo 49. -/
theorem eligibleResidue_of_mod_eq {a b : ℤ} (h : a % 49 = b % 49)
    (hb : EligibleResidue b) : EligibleResidue a := by
  unfold EligibleResidue at *
  omega

end FibonacciCriterion.Eligibility
