import FibonacciCriterion.Fibonacci.ValuationInputs
import FibonacciCriterion.Fibonacci.Growth
import FibonacciCriterion.Regular.TwoAdicSubtraction

/-!
# Fibonacci members of the 2-adic families (Lemmas 2.4 and 5.3)

A kernel-checked table of `v₂(Fₙ)` and `u₂(Fₙ)` for `n ≤ 64`
(`normalization_checked`, `members_checked`) locates the members of the
families `E_{0,7}`, `E_{1,7}`, `E_{1,5}` among `F₁, …, F₆₄`:

* a member of `E_{0,7}` has index 10, 22, or at least 34;
* a member of `E_{1,7}` has index 42;
* a member of `E_{1,5}` has index 30.

This gives the 2-adic rows of Lemma 2.4 and the finite part of Lemma 5.3. The
manuscript obtains these lists from the valuation formula of Lemma 2.2 and the
residues of a few Fibonacci numbers; here they are read from the table. In
Lemma 5.3, the case `F₂₂ = 17711` is checked directly, and the bound (1),
`2^{v₂(Fₙ)} ≤ 4n`, with Lemma 2.1 gives the rest from the indices 34 and 64
(`room_of_growth`). At 22 the manuscript uses `F₂₂ > 4 · 22 · 55` for
`⟨1,1,1⟩` and `F₂₂ > 16 · 880` for `⟨1,2,2⟩`; here `F₂₂ ≥ 16 q̄_T` for
`q̄_T ≤ 880` covers both.
-/

namespace FibonacciCriterion

open TwoAdic

namespace TwoAdicFibonacci

/-- The table of `v₂(Fₙ)` for `1 ≤ n ≤ 64`. The entry at 0 is 0. -/
def exponent : Fin 65 → ℕ :=
  ![0,0,0,1,0,0,3,0,0,1,0,0,4,0,0,1,0,0,3,0,0,1,0,0,5,0,0,1,0,0,3,0,
    0,1,0,0,4,0,0,1,0,0,3,0,0,1,0,0,6,0,0,1,0,0,3,0,0,1,0,0,4,0,0,1,
    0]

/-- The table of the odd parts `u₂(Fₙ)`, with `Fₙ = 2^{v₂(Fₙ)} u₂(Fₙ)`, for
`1 ≤ n ≤ 64`. The entry at 0 is 0. -/
def unit : Fin 65 → ℕ :=
  ![0,1,1,1,3,5,
    1,13,21,17,55,89,
    9,233,377,305,987,1597,
    323,4181,6765,5473,17711,28657,
    1449,75025,121393,98209,317811,514229,
    104005,1346269,2178309,1762289,5702887,9227465,
    933147,24157817,39088169,31622993,102334155,165580141,
    33489287,433494437,701408733,567451585,1836311903,2971215073,
    75117609,7778742049,12586269025,10182505537,32951280099,53316291173,
    10783446409,139583862445,225851433717,182717648081,591286729879,956722026041,
    96750547245,2504730781961,4052739537881,3278735159921,10610209857723]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The tables are correct: for `1 ≤ n ≤ 64`, `Fₙ = 2^{exponent n} · unit n`
and `unit n` is odd. -/
theorem normalization_checked : ∀ i : Fin 65, i.val = 0 ∨
    (Nat.fib i.val = 2 ^ exponent i * unit i ∧ unit i % 2 = 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The table entries that match the three families: an index `i ≤ 64` whose
exponent parity and odd part modulo 8 match `E_{0,7}` is 10, 22, or at least
34; matching `E_{1,7}`, it is 42; matching `E_{1,5}`, it is 30. -/
theorem members_checked : ∀ i : Fin 65,
    (exponent i % 2 = 0 → unit i % 8 = 7 →
      i.val = 10 ∨ i.val = 22 ∨ 34 ≤ i.val) ∧
    (exponent i % 2 = 1 → unit i % 8 = 7 → i.val = 42) ∧
    (exponent i % 2 = 1 → unit i % 8 = 5 → i.val = 30) := by
  decide +kernel

/-- If `Fₙ = 2^a u` with `u` odd belongs to `E_{ε,r}`, then `a ≡ ε (mod 2)` and
`u ≡ r (mod 8)`. -/
theorem signature_of_exceptional {n a u ε : ℕ} {r : ℤ}
    (hfac : Nat.fib n = 2 ^ a * u) (hu : u % 2 = 1)
    (hex : TwoAdicExceptional ε r (Nat.fib n : ℤ)) :
    a % 2 = ε % 2 ∧ (u : ℤ) % 8 = r % 8 := by
  obtain ⟨_, b, v, hvfac, hvodd, hb, hvr⟩ := hex
  have hfacZ : (Nat.fib n : ℤ) = (2 : ℤ) ^ a * (u : ℤ) := by
    exact_mod_cast hfac
  have huZ : (u : ℤ) % 2 = 1 := by exact_mod_cast hu
  obtain ⟨rfl, rfl⟩ := pow_two_odd_unique huZ hvodd (hfacZ.symm.trans hvfac)
  exact ⟨hb, hvr⟩

/-- For `n < 65`, if `Fₙ ∈ E_{ε,r}`, the table entries at `n` have exponent
`≡ ε (mod 2)` and odd part `≡ r (mod 8)`. -/
theorem signature_at {n : ℕ} (hn : n < 65) {ε : ℕ} {r : ℤ}
    (hex : TwoAdicExceptional ε r (Nat.fib n : ℤ)) :
    exponent ⟨n, hn⟩ % 2 = ε % 2 ∧
      ((unit ⟨n, hn⟩ : ℕ) : ℤ) % 8 = r % 8 := by
  rcases normalization_checked ⟨n, hn⟩ with h0 | ⟨hfac, hu⟩
  · have : n = 0 := h0
    subst this
    exact absurd hex.1 (by simp)
  · exact signature_of_exceptional hfac hu hex

/-- A Fibonacci member of `E_{0,7}` has index 10, 22, or at least 34. -/
theorem member_even_seven (n : ℕ)
    (hex : TwoAdicExceptional 0 7 (Nat.fib n : ℤ)) :
    n = 10 ∨ n = 22 ∨ 34 ≤ n := by
  by_cases hn : n < 65
  · obtain ⟨h1, h2⟩ := signature_at hn hex
    exact (members_checked ⟨n, hn⟩).1 (by omega) (by omega)
  · omega

/-- A Fibonacci member of `E_{1,7}` has index 42 or at least 64. -/
theorem member_odd_seven (n : ℕ)
    (hex : TwoAdicExceptional 1 7 (Nat.fib n : ℤ)) : n = 42 ∨ 64 ≤ n := by
  by_cases hn : n < 64
  · obtain ⟨h1, h2⟩ := signature_at (by omega : n < 65) hex
    exact Or.inl ((members_checked ⟨n, by omega⟩).2.1 (by omega) (by omega))
  · omega

/-- A Fibonacci member of `E_{1,5}` has index 30 or at least 64. -/
theorem member_odd_five (n : ℕ)
    (hex : TwoAdicExceptional 1 5 (Nat.fib n : ℤ)) : n = 30 ∨ 64 ≤ n := by
  by_cases hn : n < 64
  · obtain ⟨h1, h2⟩ := signature_at (by omega : n < 65) hex
    exact Or.inl ((members_checked ⟨n, by omega⟩).2.2 (by omega) (by omega))
  · omega

/-- Lemma 2.4 for `E_{1,7}`: no Fibonacci number below `F₄₂` belongs to
`E_{1,7}`. -/
theorem no_odd_seven_exception_below_forty_two (n : ℕ) (hn : n < 42) :
    ¬ TwoAdicExceptional 1 7 (Nat.fib n : ℤ) := fun hex => by
  rcases member_odd_seven n hex with h | h <;> omega

/-- Lemma 2.4 for `E_{1,5}`: no Fibonacci number below `F₃₀` belongs to
`E_{1,5}`. -/
theorem no_odd_five_exception_below_thirty (n : ℕ) (hn : n < 30) :
    ¬ TwoAdicExceptional 1 5 (Nat.fib n : ℤ) := fun hex => by
  rcases member_odd_five n hex with h | h <;> omega

/-- Lemma 5.3 (i) for `E_{1,7}` and `E_{1,5}`: every Fibonacci member has
valuation at least 3. Valuation 1 would give `Fₙ ≡ 14` or `10 (mod 16)`, and no
Fibonacci number has these residues. -/
theorem three_le_of_odd (n a : ℕ) (u : ℤ) {r : ℤ} (hr : r = 7 ∨ r = 5)
    (hfac : (Nat.fib n : ℤ) = 2 ^ a * u) (ha : a % 2 = 1) (hur : u % 8 = r % 8) :
    3 ≤ a := by
  by_contra h
  have ha1 : a = 1 := by omega
  subst ha1
  rcases hr with rfl | rfl
  · exact FibonacciValuationInputs.two_unit_not_seven_of_exponent_one n u
      (by simpa using hfac) (by omega)
  · exact FibonacciValuationInputs.two_unit_not_five_of_exponent_one n u
      (by simpa using hfac) (by omega)

/-- The growth step of Lemma 5.3: from `Fₘ ≥ 4 m C` at one index `m ≥ 4`,
the bound (1) and Lemma 2.1 give `Fₙ ≥ 2^{max(4, v₂ Fₙ)} C` for all
`n ≥ m`. -/
theorem room_of_growth (iv : FibonacciValuationInputs) {m n : ℕ} (hm : 4 ≤ m)
    (hmn : m ≤ n) (C : ℤ) (hC0 : 0 ≤ C)
    (hC : 4 * m * C ≤ Nat.fib m) (a : ℕ) (u : ℤ)
    (hfac : (Nat.fib n : ℤ) = 2 ^ a * u) (hu : u % 2 = 1) :
    2 ^ max 4 a * C ≤ Nat.fib n := by
  obtain ⟨a', u', hfac', hu', hbound⟩ :=
    FibonacciValuationInputs.two_prime_power_bound iv n (by omega)
  have hu'Z : ((u' : ℕ) : ℤ) % 2 = 1 := by exact_mod_cast hu'
  have hfac'Z : (Nat.fib n : ℤ) = 2 ^ a' * (u' : ℤ) := by exact_mod_cast hfac'
  have ha : a = a' := (pow_two_odd_unique hu hu'Z (hfac.symm.trans hfac'Z)).1
  subst ha
  have h4n : (2 : ℤ) ^ max 4 a ≤ 4 * n := by
    rcases le_total 4 a with h | h
    · rw [max_eq_right h]
      exact_mod_cast hbound
    · rw [max_eq_left h]
      norm_num
      omega
  have hgrowth : (Nat.fib m : ℤ) * n ≤ Nat.fib n * m := by
    exact_mod_cast fib_mul_le_of_le (by omega : 2 ≤ m) hmn
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
  have h1 : 4 * (n : ℤ) * C ≤ Nat.fib n := by
    have : 4 * (n : ℤ) * C * m ≤ Nat.fib n * m := by nlinarith
    exact le_of_mul_le_mul_right this hm0
  calc 2 ^ max 4 a * C ≤ 4 * (n : ℤ) * C := mul_le_mul_of_nonneg_right h4n hC0
    _ ≤ Nat.fib n := h1

/-- Lemma 5.3 (ii) for `E_{0,7}`: for `0 ≤ q̄_T ≤ 4455`, every member `Fₙ > F₁₀`
satisfies `Fₙ ≥ 2^{max(4, v₂ Fₙ)} q̄_T`, except `F₂₂` when `q̄_T > 880`. The
escalators `⟨1,1,1⟩`, `⟨1,2,2⟩`, `g` have `q̄_T = 55, 880, 4455`. -/
theorem size_bound_even_seven (iv : FibonacciValuationInputs) (n a : ℕ) (u : ℤ)
    (hfac : (Nat.fib n : ℤ) = 2 ^ a * u) (hu : u % 2 = 1)
    (hex : TwoAdicExceptional 0 7 (Nat.fib n : ℤ)) (hn : n ≠ 10)
    (qbd : ℤ) (hq0 : 0 ≤ qbd) (hq : qbd ≤ 4455) (h22 : n = 22 → qbd ≤ 880) :
    2 ^ max 4 a * qbd ≤ Nat.fib n := by
  rcases member_even_seven n hex with h | rfl | h
  · exact absurd h hn
  · -- `F₂₂ = 17711` is odd, so the factor is `16`.
    have h22v : (Nat.fib 22 : ℤ) = 2 ^ 0 * 17711 := by norm_num [Nat.fib_add_two]
    have ha : a = 0 := (pow_two_odd_unique hu (by norm_num) (hfac.symm.trans h22v)).1
    subst ha
    rw [h22v]
    have := h22 rfl
    norm_num
    omega
  · exact room_of_growth iv (m := 34) (by norm_num) h qbd hq0
      (by norm_num [Nat.fib_add_two]; omega) a u hfac hu

/-- Lemma 5.3 (ii) for `E_{1,7}` and `E_{1,5}`: for `0 ≤ q̄_T ≤ 64 F₄₂`, every
member after the truant has index at least 64 and satisfies
`Fₙ ≥ 2^{max(4, v₂ Fₙ)} q̄_T`. The escalators `⟨1,1,2⟩`, `⟨1,2,4⟩` (family
`E_{1,7}`) and `⟨1,2,3⟩` (family `E_{1,5}`) have
`q̄_T = 4 F₄₂, 64 F₄₂, 36 F₃₀`. -/
theorem size_bound_odd (iv : FibonacciValuationInputs) (n a : ℕ) (u : ℤ)
    (hfac : (Nat.fib n : ℤ) = 2 ^ a * u) (hu : u % 2 = 1)
    (hmem : (TwoAdicExceptional 1 7 (Nat.fib n : ℤ) ∧ n ≠ 42) ∨
      (TwoAdicExceptional 1 5 (Nat.fib n : ℤ) ∧ n ≠ 30))
    (qbd : ℤ) (hq0 : 0 ≤ qbd) (hq : qbd ≤ 64 * 267914296) :
    2 ^ max 4 a * qbd ≤ Nat.fib n := by
  have h64 : 64 ≤ n := by
    rcases hmem with ⟨hex, hn⟩ | ⟨hex, hn⟩
    · rcases member_odd_seven n hex with h | h <;> omega
    · rcases member_odd_five n hex with h | h <;> omega
  exact room_of_growth iv (m := 64) (by norm_num) h64 qbd hq0
    (by norm_num [Nat.fib_add_two]; omega) a u hfac hu

/-- Lemma 2.2 at 2: for `n ≥ 1`, an even valuation `v₂(Fₙ)` is 0 or at least 4
(valuation 2 does not occur). This is
`FibonacciValuationInputs.two_even_exponent_zero_or_four_le` for an integer odd
part. -/
theorem even_valuation_zero_or_four_le (iv : FibonacciValuationInputs) (n a : ℕ)
    (u : ℤ) (hn : 1 ≤ n) (hfac : (Nat.fib n : ℤ) = 2 ^ a * u) (hu : u % 2 = 1)
    (heven : a % 2 = 0) : a = 0 ∨ 4 ≤ a := by
  obtain ⟨a', u', hfac', hu', -⟩ :=
    FibonacciValuationInputs.two_prime_power_bound iv n hn
  have hu'Z : ((u' : ℕ) : ℤ) % 2 = 1 := by exact_mod_cast hu'
  have hfac'Z : (Nat.fib n : ℤ) = 2 ^ a' * (u' : ℤ) := by exact_mod_cast hfac'
  have ha : a = a' := (pow_two_odd_unique hu hu'Z (hfac.symm.trans hfac'Z)).1
  subst ha
  exact FibonacciValuationInputs.two_even_exponent_zero_or_four_le iv n a u' hn
    hfac' hu' heven

end TwoAdicFibonacci

end FibonacciCriterion
