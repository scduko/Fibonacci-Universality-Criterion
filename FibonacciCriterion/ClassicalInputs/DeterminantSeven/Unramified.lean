import FibonacciCriterion.ClassicalInputs.DeterminantSeven.GramMatrices
import FibonacciCriterion.ClassicalInputs.Mordell
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Representation by `f` or `h`: the unramified case `7 ∤ n` (Proposition 3.3)

For a positive integer `n` with `7 ∤ n`, `exists_unramifiedWitness`
constructs the entries of `unramifiedGram`. By Dirichlet's theorem there
is an auxiliary prime `q > 7n` with

* `q ≡ -1 (mod 8n)`,
* `q ≡ 1 (mod 7)`.

The first congruence makes `a = (q + 1)/n` an integer and, since
`q ≡ 7 (mod 8)`, gives `(n/q) = 1`. The second gives `(-7/q) = 1`. Hence `-7n`
has a square root `L` modulo `q`, and `c = (7 + aL²)/q` is an integer. In the
manuscript's notation, `n` is `N`, the prime `q` is `ℓ`, `L` is `λ`, and `a`,
`c` are `a₀`, `c₀`.
-/

namespace FibonacciCriterion.DeterminantSevenGenus

open MordellRegularity

/-- If a prime `q` satisfies `q ≡ 7 (mod 8)` and `q ≡ -1 (mod n)`, then
`(n/q) = 1`. The proof removes factors of 2 and applies Jacobi reciprocity
to the odd part. -/
theorem legendre_nat_eq_one_of_mod_neg_one
    {n q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hq8 : q % 8 = 7) (hqn : q ≡ n - 1 [MOD n]) :
    @legendreSym q ⟨hq⟩ (n : ℤ) = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases heven : n % 2 = 0
      · let m := n / 2
        have hnm : n = 2 * m := by
          dsimp [m]
          omega
        have hmpos : 0 < m := by omega
        have hmlt : m < n := by omega
        have hqm : q ≡ m - 1 [MOD m] := by
          have hd : m ∣ n := by
            rw [hnm]
            exact dvd_mul_left m 2
          have ht := hqn.of_dvd hd
          change q % m = (m - 1) % m
          change q % m = (n - 1) % m at ht
          have hmrem : (n - 1) % m = (m - 1) % m := by
            have heq : 2 * m - 1 = m + (m - 1) := by omega
            rw [hnm, heq, Nat.add_mod]
            simp [Nat.mod_eq_of_lt (show m - 1 < m by omega)]
          exact ht.trans hmrem
        have hi := ih m hmlt hmpos hqm
        have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
        have htwo : jacobiSym (2 : ℤ) q = 1 := by
          rw [jacobiSym.at_two hqodd, ZMod.χ₈_nat_eq_if_mod_eight]
          split_ifs <;> omega
        rw [jacobiSym.legendreSym.to_jacobiSym,
          show (n : ℤ) = 2 * (m : ℤ) by exact_mod_cast hnm,
          jacobiSym.mul_left, htwo]
        simpa [jacobiSym.legendreSym.to_jacobiSym] using hi
      · have hodd : Odd n := Nat.odd_iff.mpr (by omega)
        have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
        have hq4 : q % 4 = 3 := by omega
        have hswap : jacobiSym (q : ℤ) n = jacobiSym (-1) n := by
          exact jacobi_of_separator_residue (d := 1) (c := 1) hqn (by omega)
        have hswap' : jacobiSym (q : ℤ) n = ZMod.χ₄ n := by
          rw [hswap, jacobiSym.neg _ hodd]
          norm_num
        rw [jacobiSym.legendreSym.to_jacobiSym]
        rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with hn4 | hn4
        · rw [jacobiSym.quadratic_reciprocity_one_mod_four hn4 hqodd,
            hswap', ZMod.χ₄_nat_one_mod_four hn4]
        · rw [jacobiSym.quadratic_reciprocity_three_mod_four hn4 hq4,
            hswap', ZMod.χ₄_nat_three_mod_four hn4]
          ring

/-- If a prime `q` satisfies `q ≡ 7 (mod 8)`, `q ≡ 1 (mod 7)`, and
`q ≡ -1 (mod n)`, then `(-7n/q) = 1`. -/
theorem legendre_neg_seven_mul_eq_one
    {n q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hq8 : q % 8 = 7) (hq7 : q % 7 = 1)
    (hqn : q ≡ n - 1 [MOD n]) :
    @legendreSym q ⟨hq⟩ (-(7 * (n : ℤ))) = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hq4 : q % 4 = 3 := by omega
  have hnleg := legendre_nat_eq_one_of_mod_neg_one hn hq hq8 hqn
  have h7 : jacobiSym (-7) q = 1 := by
    rw [show (-7 : ℤ) = -((7 : ℕ) : ℤ) by norm_num,
      jacobiSym.neg _ hqodd, ZMod.χ₄_nat_three_mod_four hq4,
      jacobiSym.quadratic_reciprocity_three_mod_four
        (by norm_num : (7 : ℕ) % 4 = 3) hq4,
      jacobiSym.mod_left]
    have hqmod : (q : ℤ) % ((7 : ℕ) : ℤ) = 1 := by
      exact_mod_cast hq7
    rw [hqmod]
    norm_num
  rw [jacobiSym.legendreSym.to_jacobiSym,
    show -(7 * (n : ℤ)) = (-7) * (n : ℤ) by ring,
    jacobiSym.mul_left, h7, one_mul]
  simpa [jacobiSym.legendreSym.to_jacobiSym] using hnleg

/-- The auxiliary prime: for `n > 0` with `7 ∤ n`, Dirichlet's theorem gives a
prime `q > 7n` with `q ≡ -1 (mod 8n)` and `q ≡ 1 (mod 7)`, stated as
`q ≡ 7 (mod 8)`, `q ≡ 1 (mod 7)`, and `q ≡ -1 (mod n)`. -/
theorem exists_unramified_seven_auxiliary_prime
    {n : ℕ} (hn : 0 < n) (h7n : ¬ 7 ∣ n) :
    ∃ q : ℕ, 7 * n < q ∧ q.Prime ∧ q % 8 = 7 ∧
      q % 7 = 1 ∧ q ≡ n - 1 [MOD n] := by
  have hn7 : n.Coprime 7 := by
    rw [Nat.coprime_comm, Nat.prime_seven.coprime_iff_not_dvd]
    exact h7n
  have hM7 : (8 * n).Coprime 7 :=
    (by norm_num : Nat.Coprime 8 7).mul_left hn7
  have hpred : (8 * n - 1).Coprime (8 * n) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    let d := (8 * n - 1).gcd (8 * n)
    have hdleft : d ∣ 8 * n - 1 := Nat.gcd_dvd_left _ _
    have hdright : d ∣ 8 * n := Nat.gcd_dvd_right _ _
    have hdone : d ∣ 1 := by
      apply (Nat.dvd_add_iff_right hdleft).mpr
      have heq : (8 * n - 1) + 1 = 8 * n := by omega
      rw [heq]
      exact hdright
    exact Nat.dvd_one.mp hdone
  let R := Nat.chineseRemainder hM7 (8 * n - 1) 1
  have hRM : (R : ℕ).Coprime (8 * n) :=
    coprime_of_modEq R.prop.1 hpred
  have hR7 : (R : ℕ).Coprime 7 :=
    coprime_of_modEq R.prop.2 (by norm_num)
  obtain ⟨q, hqbig, hqprime, hqR⟩ :=
    exists_auxiliary_prime (max (R : ℕ) (7 * n)) ((8 * n) * 7) R
      (by positivity) (hRM.mul_right hR7)
  have hqM : q ≡ 8 * n - 1 [MOD 8 * n] :=
    (hqR.of_dvd (dvd_mul_right (8 * n) 7)).trans R.prop.1
  have hqseven : q ≡ 1 [MOD 7] :=
    (hqR.of_dvd (dvd_mul_left 7 (8 * n))).trans R.prop.2
  have hq8 : q % 8 = 7 := by
    have ht := hqM.of_dvd (dvd_mul_right 8 n)
    change q % 8 = (8 * n - 1) % 8 at ht
    have hr : (8 * n - 1) % 8 = 7 := by omega
    exact ht.trans hr
  have hqn : q ≡ n - 1 [MOD n] := by
    have ht := hqM.of_dvd (dvd_mul_left n 8)
    change q % n = (n - 1) % n
    change q % n = (8 * n - 1) % n at ht
    have hr : (8 * n - 1) % n = (n - 1) % n := by
      have heq : 8 * n - 1 = 7 * n + (n - 1) := by omega
      rw [heq, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show n - 1 < n by omega)]
    exact ht.trans hr
  exact ⟨q, (le_max_right (R : ℕ) (7 * n)).trans_lt hqbig, hqprime,
    hq8, by simpa [Nat.ModEq] using hqseven, hqn⟩

/-- Every positive integer `n` with `7 ∤ n` has an `UnramifiedWitness`
(part of Proposition 3.3). -/
theorem exists_unramifiedWitness
    {n : ℕ} (hn : 0 < n) (h7n : ¬ 7 ∣ n) :
    Nonempty (UnramifiedWitness n) := by
  obtain ⟨q, hqbig, hqprime, hq8, hq7, hqn⟩ :=
    exists_unramified_seven_auxiliary_prime hn h7n
  have hqrem : q % n = n - 1 := by
    change q % n = (n - 1) % n at hqn
    exact hqn.trans (Nat.mod_eq_of_lt (show n - 1 < n by omega))
  have hdiva : n ∣ q + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    by_cases hn1 : n = 1
    · subst n
      exact Nat.mod_one (q + 1)
    · have hone : 1 < n := by omega
      rw [Nat.add_mod, hqrem, Nat.mod_eq_of_lt hone]
      simp [show n - 1 + 1 = n by omega]
  obtain ⟨a, ha⟩ := hdiva
  have : Fact q.Prime := ⟨hqprime⟩
  have hnonzero : (((7 * n : ℕ) : ℤ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdz : (q : ℤ) ∣ ((7 * n : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hdvd : q ∣ 7 * n := by exact_mod_cast hdvdz
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) hqbig) hdvd
  have hleg : legendreSym q (-(7 * (n : ℤ))) = 1 :=
    legendre_neg_seven_mul_eq_one hn hqprime hq8 hq7 hqn
  have hsqrt : HasNegSquareRoot (7 * n) q :=
    hasNegSquareRoot_of_legendreSym
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat, Int.cast_neg] using
        (neg_ne_zero.mpr hnonzero)) hleg
  obtain ⟨L, hL⟩ := hsqrt.exists_int_dvd
  rcases hL with ⟨t, ht⟩
  have haZ : (n : ℤ) * (a : ℤ) = (q : ℤ) + 1 := by
    exact_mod_cast ha.symm
  have hcdiv : (q : ℤ) ∣ 7 + (a : ℤ) * L ^ 2 := by
    refine ⟨(a : ℤ) * t - 7, ?_⟩
    push_cast at ht
    linear_combination (a : ℤ) * ht - 7 * haZ
  obtain ⟨c, hc⟩ := hcdiv
  exact ⟨
    { q := q
      a := a
      L := L
      c := c
      q_pos := by exact_mod_cast hqprime.pos
      q_mod_seven := by
        rw [Int.cast_natCast]
        simpa only [Nat.cast_one] using
          (ZMod.natCast_eq_natCast_iff' q 1 7).mpr hq7
      quotient_a := haZ
      quotient_c := hc.symm }⟩

/-- `exists_unramifiedWitness`, in the form of `UnramifiedSevenArithmetic`. -/
theorem unramifiedSevenArithmetic : UnramifiedSevenArithmetic := by
  intro n hn hmod
  apply exists_unramifiedWitness hn.1
  intro hdiv
  exact hmod (Nat.dvd_iff_mod_eq_zero.mp hdiv)

end FibonacciCriterion.DeterminantSevenGenus
