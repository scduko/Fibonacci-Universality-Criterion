import FibonacciCriterion.ClassicalInputs.DeterminantSeven.GramMatrices
import FibonacciCriterion.ClassicalInputs.Mordell
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Representation by `f` or `h`: the ramified case `n = 7u` (Proposition 3.3)

For an eligible `n = 7u` with `u ≡ 1, 2, 4 (mod 7)`,
`exists_ramifiedWitness` constructs the entries of `ramifiedGram`.
By Dirichlet's theorem there is an auxiliary prime `p > 8u` with
`p ≡ -7 (mod 8u)`. Then `p ≡ 1 (mod 8)` and `(-u/p) = 1`, so
`49d² ≡ -u (mod p)` has a solution `d`, and `a = (p + 7)/u` and
`c = (1 + 7ad²)/p` are integers. In the manuscript's notation, the prime `p`
is `ℓ`, `d` is `η`, and `a`, `c` are `a₀`, `c₀`.

The manuscript takes the prime larger than `7u` and computes `(-u/p)` through
`(m/7)`, where `m` is the odd part of `u`. Here the prime is larger than `8u`,
and `(-u/p)` is reduced by reciprocity to `(-7/v)` for the odd part `v` of `u`,
which is read off from `v` modulo 28 (`jacobi_neg_seven_of_odd_squareClass`,
used in `ramified_neg_legendre_of_progression`).
-/

namespace FibonacciCriterion.DeterminantSevenGenus

open MordellRegularity

/-- `x` is a nonzero square modulo 7: `x = 1`, 2, or 4. -/
def SevenSquareClass (x : ZMod 7) : Prop :=
  x = 1 ∨ x = 2 ∨ x = 4

private theorem sevenSquareClass_two_pow (e : ℕ) :
    SevenSquareClass ((2 : ZMod 7) ^ e) := by
  induction e with
  | zero => simp [SevenSquareClass]
  | succ e ih =>
      rcases ih with h | h | h
      · right; left
        rw [pow_succ, h]
        norm_num
      · right; right
        rw [pow_succ, h]
        norm_num
      · left
        rw [pow_succ, h]
        change (8 : ZMod 7) = 1
        decide

private theorem sevenSquareClass_cancel (x y : ZMod 7)
    (hx : SevenSquareClass x) (hxy : SevenSquareClass (x * y)) :
    SevenSquareClass y := by
  have h42 : (4 : ZMod 7) * 2 = 1 := by decide
  have h44 : (4 : ZMod 7) * 4 = 2 := by decide
  have h24 : (2 : ZMod 7) * 4 = 1 := by decide
  have h22 : (2 : ZMod 7) * 2 = 4 := by decide
  rcases hx with rfl | rfl | rfl
  · simpa using hxy
  · have hy : y = 4 * (2 * y) := by
      calc
        y = 1 * y := by simp
        _ = ((4 : ZMod 7) * 2) * y := by rw [h42]
        _ = 4 * (2 * y) := by ring
    rcases hxy with h | h | h
    · right; right
      rw [h] at hy
      simpa using hy
    · left
      rw [h, h42] at hy
      exact hy
    · right; left
      rw [h, h44] at hy
      exact hy
  · have hy : y = 2 * (4 * y) := by
      calc
        y = 1 * y := by simp
        _ = ((2 : ZMod 7) * 4) * y := by rw [h24]
        _ = 2 * (4 * y) := by ring
    rcases hxy with h | h | h
    · right; left
      rw [h] at hy
      simpa using hy
    · right; right
      rw [h, h22] at hy
      exact hy
    · left
      rw [h, h24] at hy
      exact hy

/-- For odd `v` that is a nonzero square modulo 7, `(-7/v) = 1`: the six
classes 1, 9, 11, 15, 23, 25 of `v` modulo 28. -/
private theorem jacobi_neg_seven_of_odd_squareClass {v : ℕ}
    (hv : Odd v) (hv7 : SevenSquareClass (v : ZMod 7)) :
    jacobiSym (-7) v = 1 := by
  rw [jacobiSym.mod_right (-7) hv]
  change jacobiSym (-7) (v % 28) = 1
  have hvmod7 : (v % 28) % 7 = v % 7 :=
    Nat.mod_mod_of_dvd v (by norm_num : 7 ∣ 28)
  have hvmod2 : (v % 28) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd v (by norm_num : 2 ∣ 28)]
    exact Nat.odd_iff.mp hv
  have hvres : v % 7 = 1 ∨ v % 7 = 2 ∨ v % 7 = 4 := by
    rcases hv7 with h | h | h
    · exact Or.inl (by
        simpa [Nat.ModEq] using
          (ZMod.natCast_eq_natCast_iff' v 1 7).mp h)
    · exact Or.inr (Or.inl (by
        simpa [Nat.ModEq] using
          (ZMod.natCast_eq_natCast_iff' v 2 7).mp h))
    · exact Or.inr (Or.inr (by
        simpa [Nat.ModEq] using
          (ZMod.natCast_eq_natCast_iff' v 4 7).mp h))
  have hhi : v % 28 < 28 := Nat.mod_lt _ (by norm_num)
  rcases hvres with h1 | h2 | h4
  · have hr : v % 28 = 1 ∨ v % 28 = 15 := by omega
    rcases hr with hr | hr <;> rw [hr] <;> norm_num
  · have hr : v % 28 = 9 ∨ v % 28 = 23 := by omega
    rcases hr with hr | hr <;> rw [hr] <;> norm_num
  · have hr : v % 28 = 11 ∨ v % 28 = 25 := by omega
    rcases hr with hr | hr <;> rw [hr] <;> norm_num

/-- If `u > 0` is a nonzero square modulo 7 and `p` is a prime with
`p ≡ 1 (mod 8)` and `p ≡ -7 (mod u)`, then `(-u/p) = 1`. -/
theorem ramified_neg_legendre_of_progression {u p : ℕ}
    (hu : 0 < u)
    (hu7 : SevenSquareClass (u : ZMod 7))
    (hp : p.Prime) (hp8 : p % 8 = 1)
    (hpu : p ≡ 8 * u - 7 [MOD u]) :
    @legendreSym p ⟨hp⟩ (-(u : ℤ)) = 1 := by
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    subst p
    norm_num at hp8
  have hpodd : Odd p := hp.odd_of_ne_two hp_ne_two
  have hp4 : p % 4 = 1 := by omega
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
  obtain ⟨e, v, hv2, huv⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hu.ne' 2 (by norm_num)
  have hvmod2 : v % 2 = 1 := by
    have hvmod2_ne : v % 2 ≠ 0 := by
      intro hzero
      exact hv2 (Nat.dvd_iff_mod_eq_zero.mpr hzero)
    have hvmod2_lt : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  have hvodd : Odd v := Nat.odd_iff.mpr hvmod2
  have he7 := sevenSquareClass_two_pow e
  have huv7 : (u : ZMod 7) = ((2 : ZMod 7) ^ e) * (v : ZMod 7) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun t : ℕ => (t : ZMod 7)) huv
  have hv7 : SevenSquareClass (v : ZMod 7) := by
    apply sevenSquareClass_cancel ((2 : ZMod 7) ^ e)
    · exact he7
    · rwa [← huv7]
  have htwo : jacobiSym 2 p = 1 := by
    rw [jacobiSym.at_two hpodd, ZMod.χ₈_nat_eq_if_mod_eight]
    simp [hp8, hp2]
  have hminus : jacobiSym (-1) p = 1 := by
    rw [jacobiSym.at_neg_one hpodd, ZMod.χ₄_nat_one_mod_four hp4]
  rw [jacobiSym.legendreSym.to_jacobiSym,
    show -(u : ℤ) = (-1) * (u : ℤ) by ring,
    jacobiSym.mul_left, hminus, one_mul, huv, Nat.cast_mul,
    jacobiSym.mul_left, Nat.cast_pow, Nat.cast_ofNat, jacobiSym.pow_left,
    htwo, one_pow, one_mul]
  rw [jacobiSym.quadratic_reciprocity_one_mod_four' hvodd hp4]
  have hvu : v ∣ u := by
    rw [huv]
    exact dvd_mul_left v (2 ^ e)
  have hpv : p ≡ 8 * u - 7 [MOD v] := hpu.of_dvd hvu
  have hid : 7 + (8 * u - 7) = v * (8 * 2 ^ e) := by
    calc
      7 + (8 * u - 7) = 8 * u := Nat.add_sub_of_le (by omega)
      _ = v * (8 * 2 ^ e) := by rw [huv]; ring
  rw [jacobi_of_separator_residue hpv hid]
  exact jacobi_neg_seven_of_odd_squareClass hvodd hv7

private theorem ramified_residue_coprime {u : ℕ}
    (hu : 0 < u) (hu7 : ¬ 7 ∣ u) :
    (8 * u - 7).Coprime (8 * u) := by
  have h7le : 7 ≤ 8 * u := by omega
  have huC : u.Coprime 7 := by
    rw [Nat.coprime_comm, Nat.prime_seven.coprime_iff_not_dvd]
    exact hu7
  have h8uC : (8 * u).Coprime 7 :=
    (by norm_num : (8 : ℕ).Coprime 7).mul_left huC
  have hr7 : (8 * u - 7).Coprime 7 :=
    (Nat.coprime_sub_self_left h7le).2 h8uC
  conv_rhs => rw [show 8 * u = 7 + (8 * u - 7) by omega]
  exact Nat.coprime_add_self_right.mpr hr7

-- The proof installs the field structure on `ZMod p` with `letI`.
set_option linter.style.haveILetI false in
/-- For `n = 7u` with `u > 0` a nonzero square modulo 7, Dirichlet's theorem
and `ramified_neg_legendre_of_progression` give a `RamifiedWitness`. -/
theorem exists_ramifiedWitness_of_data {n u : ℕ}
    (hinput : n = 7 * u) (hu : 0 < u) (hu7 : ¬ 7 ∣ u)
    (huSquare : SevenSquareClass (u : ZMod 7)) :
    Nonempty (RamifiedWitness n) := by
  let modulus := 8 * u
  let residue := 8 * u - 7
  obtain ⟨p, hup, hp, hpr⟩ :=
    exists_auxiliary_prime modulus modulus residue
      (by dsimp [modulus]; positivity)
      (ramified_residue_coprime hu hu7)
  letI : Field (ZMod p) := @ZMod.instField p ⟨hp⟩
  have hp8 : p % 8 = 1 := by
    have hmod8 := hpr.of_dvd (by
      dsimp [modulus]
      exact dvd_mul_right 8 u)
    change p % 8 = (8 * u - 7) % 8 at hmod8
    have hr : (8 * u - 7) % 8 = 1 := by omega
    exact hmod8.trans hr
  have hpu : p ≡ 8 * u - 7 [MOD u] := by
    exact hpr.of_dvd (by
      dsimp [modulus]
      exact dvd_mul_left u 8)
  have hleg : @legendreSym p ⟨hp⟩ (-(u : ℤ)) = 1 :=
    ramified_neg_legendre_of_progression hu huSquare hp hp8 hpu
  have hup' : u < p := lt_of_lt_of_le (by omega : u < 8 * u) hup.le
  have huz : (((u : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvdz : (p : ℤ) ∣ (u : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hdvd : p ∣ u := by exact_mod_cast hdvdz
    exact (Nat.not_dvd_of_pos_of_lt hu hup') hdvd
  obtain ⟨x, hx⟩ :=
    @hasNegSquareRoot_of_legendreSym u p ⟨hp⟩
      (by simpa only [Int.cast_neg] using (neg_ne_zero.mpr huz)) hleg
  have hp7 : ((7 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvdz : (p : ℤ) ∣ (7 : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hdvd : p ∣ 7 := by exact_mod_cast hdvdz
    have hpgt7 : 7 < p := lt_of_lt_of_le (by omega : 7 < 8 * u) hup.le
    exact (Nat.not_dvd_of_pos_of_lt (by norm_num) hpgt7) hdvd
  let dz : ZMod p := x * (((7 : ℤ) : ZMod p)⁻¹)
  obtain ⟨d, hd⟩ := ZMod.intCast_surjective dz
  have hdroot :
      (49 : ZMod p) * (d : ZMod p) ^ 2 + (u : ZMod p) = 0 := by
    have hx' : x ^ 2 = -(u : ZMod p) := by
      linear_combination hx
    dsimp [dz] at hd
    rw [show (49 : ZMod p) = 7 ^ 2 by norm_num, hd, mul_pow, hx']
    field_simp [hp7]
    ring
  have hp_ge_residue : 8 * u - 7 ≤ p := by omega
  have hdiva : u ∣ p + 7 := by
    have hdiff : u ∣ p - (8 * u - 7) :=
      (Nat.modEq_iff_dvd' hp_ge_residue).mp hpu.symm
    have htail : u ∣ (8 * u - 7) + 7 := by
      refine ⟨8, ?_⟩
      omega
    have hsum := dvd_add hdiff htail
    convert hsum using 1
    omega
  obtain ⟨aNat, haNat⟩ := hdiva
  have hua : (u : ℤ) * (aNat : ℤ) = (p : ℤ) + 7 := by
    exact_mod_cast haNat.symm
  have htarget : (p : ℤ) ∣ 1 + 7 * (aNat : ℤ) * d ^ 2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hzroot :
        ((7 : ZMod p) ^ 2 * (d : ZMod p) ^ 2 + (u : ZMod p)) = 0 := by
      simpa [show (49 : ZMod p) = 7 ^ 2 by norm_num] using hdroot
    have hzua : ((u : ZMod p) * (aNat : ZMod p)) = 7 := by
      have h := congrArg (fun z : ℤ => (z : ZMod p)) hua
      simpa using h
    have hmul :
        (7 : ZMod p) *
            (1 + 7 * (aNat : ZMod p) * (d : ZMod p) ^ 2) = 0 := by
      calc
        (7 : ZMod p) *
              (1 + 7 * (aNat : ZMod p) * (d : ZMod p) ^ 2) =
            (aNat : ZMod p) *
              ((7 : ZMod p) ^ 2 * (d : ZMod p) ^ 2 + (u : ZMod p)) := by
                rw [← hzua]
                ring
        _ = 0 := by rw [hzroot]; ring
    have hp7' : (7 : ZMod p) ≠ 0 := by
      simpa only [Int.cast_ofNat] using hp7
    simpa using (mul_eq_zero.mp hmul).resolve_left hp7'
  obtain ⟨c, hc⟩ := htarget
  refine ⟨{
    u := u
    a := (aNat : ℤ)
    d := d
    c := c
    p := (p : ℤ)
    input_eq := hinput
    u_pos := hu
    p_pos := by exact_mod_cast hp.pos
    u_square_mod_seven := huSquare
    quotient_a := hua
    quotient_c := ?_
  }⟩
  exact hc.symm

/-- Every `ResidualEligible` multiple of 7 has a `RamifiedWitness`
(part of Proposition 3.3). -/
theorem exists_ramifiedWitness {n : ℕ}
    (hn : Irregular.ResidualEligible n) (h7 : 7 ∣ n) :
    Nonempty (RamifiedWitness n) := by
  let u := n / 7
  have hinput : n = 7 * u := by
    dsimp [u]
    exact (Nat.mul_div_cancel' h7).symm
  have hu : 0 < u := by
    have hnpos := hn.1
    rw [hinput] at hnpos
    omega
  have hu7 : ¬ 7 ∣ u := by
    rintro ⟨k, hk⟩
    apply hn.2.1
    rw [hinput, hk]
    simp [Nat.mul_left_comm, Nat.mul_comm]
  have hur : u % 7 = 1 ∨ u % 7 = 2 ∨ u % 7 = 4 := by
    rcases hn.2.2 with hnot | h1 | h2 | h4
    · exact False.elim (hnot (Nat.dvd_iff_mod_eq_zero.mp h7))
    · left
      simpa [u] using h1
    · right; left
      simpa [u] using h2
    · right; right
      simpa [u] using h4
  have huSquare : SevenSquareClass (u : ZMod 7) := by
    rcases hur with h | h | h
    · exact Or.inl ((ZMod.natCast_eq_natCast_iff' u 1 7).mpr
        (by simpa [Nat.ModEq] using h))
    · exact Or.inr (Or.inl ((ZMod.natCast_eq_natCast_iff' u 2 7).mpr
        (by simpa [Nat.ModEq] using h)))
    · exact Or.inr (Or.inr ((ZMod.natCast_eq_natCast_iff' u 4 7).mpr
        (by simpa [Nat.ModEq] using h)))
  exact exists_ramifiedWitness_of_data hinput hu hu7 huSquare

/-- `exists_ramifiedWitness`, in the form of `RamifiedSevenArithmetic`. -/
theorem ramifiedSevenArithmetic : RamifiedSevenArithmetic := by
  intro n hn h7
  exact exists_ramifiedWitness hn
    (Nat.dvd_of_mod_eq_zero h7)

end FibonacciCriterion.DeterminantSevenGenus
