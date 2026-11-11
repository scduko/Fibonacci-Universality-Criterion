import FibonacciCriterion.Arithmetic.PrimePowerNormalization

/-!
# The 2-adic exceptional families and the subtraction table (Lemma 5.2 (ii))

`TwoAdicExceptional ε r` is the family
`E_{ε,r} = {N > 0 : v₂(N) ≡ ε (mod 2), u₂(N) ≡ r (mod 8)}` of §5.1, stated
through a factorization `N = 2^a u` with `u` odd rather than through a
valuation function.

The subtraction step of Lemma 5.2 (ii) is split by the gap between the
exponents of `N = 2^a u` and `q = 2^s ω`: five bounded rows
(`twoAdic_subtraction_near`, `|a - s| ≤ 2`, `k² ≤ 16`) and two far cases
(`twoAdic_subtraction_far_odd`, `twoAdic_subtraction_far_even`). No
representation theorem is used here; `exists_sub_escape` in
`Regular.TwoAdicEscalators` combines the cases into Lemma 5.2 (ii).
-/

namespace FibonacciCriterion.TwoAdic

/-- The exceptional family `E_{ε,r}`: `N` is positive, its 2-adic valuation is
`≡ ε (mod 2)`, and its odd part is `≡ r (mod 8)`. Only the residues of `ε`
modulo 2 and `r` modulo 8 matter. -/
def TwoAdicExceptional (ε : ℕ) (r N : ℤ) : Prop :=
  0 < N ∧ ∃ a : ℕ, ∃ u : ℤ,
    N = (2 : ℤ) ^ a * u ∧ u % 2 = 1 ∧
      a % 2 = ε % 2 ∧ u % 8 = r % 8

/-- If `X = 2^b v` with `v` odd, and either `b ≢ ε (mod 2)` or
`v ≢ r (mod 8)`, then `X` is not in `E_{ε,r}`. -/
theorem not_twoAdicExceptional_of_normalization
    (ε b : ℕ) (r X v : ℤ) (hv : v % 2 = 1)
    (hX : X = (2 : ℤ) ^ b * v)
    (hchange : b % 2 ≠ ε % 2 ∨ v % 8 ≠ r % 8) :
    ¬ TwoAdicExceptional ε r X := by
  rintro ⟨_hpos, a, u, hXu, hu, ha, hur⟩
  obtain ⟨rfl, rfl⟩ := pow_two_odd_unique hu hv (hXu.symm.trans hX)
  rcases hchange with hchange | hchange
  · exact hchange ha
  · exact hchange hur

/-- The five rows `|a - s| ≤ 2` of the subtraction table of Lemma 5.2 (ii):
some `k ≥ 1` with `k² ≤ 16` takes `N - q k²` out of `E_{ε,r}`. -/
theorem twoAdic_subtraction_near
    (ε a s : ℕ) (r N q u ω : ℤ)
    (hN : N = (2 : ℤ) ^ a * u) (hq : q = (2 : ℤ) ^ s * ω)
    (hu : u % 2 = 1) (hω : ω % 2 = 1)
    (ha : a % 2 = ε % 2) (hur : u % 8 = r % 8)
    (hnear : s = a + 2 ∨ s = a + 1 ∨ s = a ∨ a = s + 1 ∨ a = s + 2) :
    ∃ k : ℤ, 1 ≤ k ∧ k ^ 2 ≤ 16 ∧
      ¬ TwoAdicExceptional ε r (N - q * k ^ 2) := by
  rcases hnear with h | h | h | h | h
  · subst s
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    apply not_twoAdicExceptional_of_normalization ε a r _ (u - 4 * ω)
    · omega
    · rw [hN, hq, pow_add]; norm_num; ring
    · right; omega
  · subst s
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    apply not_twoAdicExceptional_of_normalization ε a r _ (u - 2 * ω)
    · omega
    · rw [hN, hq, pow_add]; norm_num; ring
    · right; omega
  · subst s
    refine ⟨2, by norm_num, by norm_num, ?_⟩
    apply not_twoAdicExceptional_of_normalization ε a r _ (u - 4 * ω)
    · omega
    · rw [hN, hq]; ring
    · right; omega
  · subst a
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    apply not_twoAdicExceptional_of_normalization ε s r _ (2 * u - ω)
    · omega
    · rw [hN, hq, pow_add]; norm_num; ring
    · left; omega
  · subst a
    refine ⟨4, by norm_num, by norm_num, ?_⟩
    apply not_twoAdicExceptional_of_normalization ε (s + 2) r _ (u - 4 * ω)
    · omega
    · rw [hN, hq, pow_add]; norm_num; ring
    · right; omega

/-- When `a - s = 2t + 3` (odd and at least 3), subtracting `q` changes the
parity of the 2-adic valuation, so `N - q` is not in `E_{ε,r}`. -/
theorem twoAdic_subtraction_far_odd
    (ε s t : ℕ) (r N q u ω : ℤ)
    (hN : N = (2 : ℤ) ^ (s + (2 * t + 3)) * u)
    (hq : q = (2 : ℤ) ^ s * ω)
    (hω : ω % 2 = 1) (ha : (s + (2 * t + 3)) % 2 = ε % 2) :
    ¬ TwoAdicExceptional ε r (N - q) := by
  apply not_twoAdicExceptional_of_normalization ε s r _
    ((2 : ℤ) ^ (2 * t + 3) * u - ω)
  · have hp : ((2 : ℤ) ^ (2 * t + 3) * u) % 2 = 0 := by
      rw [show 2 * t + 3 = (2 * t + 2) + 1 by omega, pow_succ]
      norm_num [Int.mul_emod]
    omega
  · rw [hN, hq, pow_add]
    ring
  · left
    intro hsame
    rw [Nat.add_mod] at ha
    have htmod : (2 * t + 3) % 2 = 1 := by omega
    rw [htmod] at ha
    omega

/-- When `a - s = 2t + 4` (even and at least 4), the odd parts of `N - q k²`
for `k = 1` and `k = 2^(t+1)` (the manuscript's `k₀`) differ by 4 modulo 8, so
one of the two differences is not in `E_{ε,r}`. -/
theorem twoAdic_subtraction_far_even
    (ε s t : ℕ) (r N q u ω : ℤ)
    (hN : N = (2 : ℤ) ^ (s + (2 * t + 4)) * u)
    (hq : q = (2 : ℤ) ^ s * ω)
    (hu : u % 2 = 1) (hω : ω % 2 = 1) :
    ∃ k : ℤ, (k = 1 ∨ k = (2 : ℤ) ^ (t + 1)) ∧
      ¬ TwoAdicExceptional ε r (N - q * k ^ 2) := by
  let v₁ := (2 : ℤ) ^ (2 * t + 4) * u - ω
  let v₂ := 4 * u - ω
  have hv₁ : v₁ % 2 = 1 := by
    dsimp [v₁]
    have hp : ((2 : ℤ) ^ (2 * t + 4) * u) % 2 = 0 := by
      rw [show 2 * t + 4 = (2 * t + 3) + 1 by omega, pow_succ]
      norm_num [Int.mul_emod]
    omega
  have hv₂ : v₂ % 2 = 1 := by dsimp [v₂]; omega
  have hres₁ : N - q = (2 : ℤ) ^ s * v₁ := by
    dsimp [v₁]
    rw [hN, hq, pow_add]
    ring
  have hres₂ : N - q * ((2 : ℤ) ^ (t + 1)) ^ 2 =
      (2 : ℤ) ^ (s + (2 * t + 2)) * v₂ := by
    dsimp [v₂]
    have hk : ((2 : ℤ) ^ (t + 1)) ^ 2 = (2 : ℤ) ^ (2 * t + 2) := by
      calc
        ((2 : ℤ) ^ (t + 1)) ^ 2 = (2 : ℤ) ^ ((t + 1) * 2) := by
          rw [pow_mul]
        _ = (2 : ℤ) ^ (2 * t + 2) := by
          congr 1
          omega
    have hbig : (2 : ℤ) ^ (s + (2 * t + 4)) =
        (2 : ℤ) ^ (s + (2 * t + 2)) * 4 := by
      rw [show s + (2 * t + 4) = (s + (2 * t + 2)) + 2 by omega,
        pow_add]
      norm_num
    have hprod : (2 : ℤ) ^ s * (2 : ℤ) ^ (2 * t + 2) =
        (2 : ℤ) ^ (s + (2 * t + 2)) :=
      (pow_add (2 : ℤ) s (2 * t + 2)).symm
    rw [hN, hq, hk, hbig]
    rw [show (2 : ℤ) ^ s * ω * (2 : ℤ) ^ (2 * t + 2) =
        ((2 : ℤ) ^ s * (2 : ℤ) ^ (2 * t + 2)) * ω by ring, hprod]
    ring
  by_cases hr₁ : v₁ % 8 = r % 8
  · refine ⟨(2 : ℤ) ^ (t + 1), Or.inr rfl, ?_⟩
    apply not_twoAdicExceptional_of_normalization ε (s + (2 * t + 2)) r _ v₂
      hv₂ hres₂
    right
    dsimp [v₁, v₂] at hr₁ ⊢
    have hp : ((2 : ℤ) ^ (2 * t + 4) * u) % 8 = 0 := by
      rw [show 2 * t + 4 = 3 + (2 * t + 1) by omega, pow_add]
      norm_num
      refine ⟨(2 : ℤ) ^ (2 * t + 1) * u, ?_⟩
      ring
    omega
  · refine ⟨1, Or.inl rfl, ?_⟩
    simpa using not_twoAdicExceptional_of_normalization ε s r _ v₁ hv₁ hres₁
      (Or.inr hr₁)

end FibonacciCriterion.TwoAdic
