import FibonacciCriterion.Irregular.Transfers

/-!
# Primality of the transfer primes

The matrix identities of Table 3 do not show that the entries of
`transferPrimes` are prime. `transfer_prime_facts_checked` verifies by kernel
evaluation that each is a prime different from 7; Lemma 6.5 uses this for the
lift modulo `p²` and the Chinese remainder theorem.
-/

namespace FibonacciCriterion.Irregular

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Each entry of `transferPrimes` is a prime other than 7. -/
theorem transfer_prime_facts_checked :
    transferPrimes.all (fun p => decide
      (Nat.Prime p.toNat ∧ Nat.Coprime p.toNat 7)) = true := by
  decide +kernel

/-- Every member of `transferPrimes`, as a natural number, is prime and prime
to 7. -/
theorem transfer_prime_facts (p : ℕ) (hp : (p : ℤ) ∈ transferPrimes) :
    Nat.Prime p ∧ Nat.Coprime p 7 := by
  have h := List.all_eq_true.mp transfer_prime_facts_checked (p : ℤ) hp
  simpa using h

end FibonacciCriterion.Irregular
