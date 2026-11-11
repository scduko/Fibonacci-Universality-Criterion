import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

/-!
# Square roots for the `⟨1,2,3⟩` Mordell construction

This file collects the square-root lemmas of the Mordell construction for
`⟨1,2,3⟩`. For odd `m`, a solution `A` of `9m ∣ A² + a - 3m` can be taken even
(`exists_even_123_strong_root`; in the names of this file such an `A` is a
strong root). At the auxiliary prime `p`, a square root of
`-6m` gives `t` with `p ∣ 6 + mt²` (`exists_123_binary_dvd_of_legendre`), the
binary completion; for the coefficient `2p` the same root gives
`2p ∣ 6 + 2m₁t²` (`exists_123_twice_binary_dvd_of_legendre`).
-/

namespace FibonacciCriterion.Regular123SquareRoots

/-- The integer `c` is a square modulo `n`. -/
def HasSquareRootMod (c : ℤ) (n : ℕ) : Prop :=
  ∃ x : ZMod n, x ^ 2 = (c : ZMod n)

/-- If `9m ∣ A² + a - 3m`, then `m ∣ A² + a`, so the leading coefficient
`(A² + a)/m` is an integer. -/
theorem xx_dvd_of_123_strong_root {m a A : ℤ}
    (h : 9 * m ∣ A ^ 2 + a - 3 * m) :
    m ∣ A ^ 2 + a := by
  rcases h with ⟨k, hk⟩
  refine ⟨9 * k + 3, ?_⟩
  calc
    A ^ 2 + a = (A ^ 2 + a - 3 * m) + 3 * m := by ring
    _ = (9 * m) * k + 3 * m := by rw [hk]
    _ = m * (9 * k + 3) := by ring

/-- If `M ∣ x² - c` and `y ≡ x (mod M)`, then `M ∣ y² - c`. -/
theorem square_root_dvd_of_congruent {M c x y : ℤ}
    (hx : M ∣ x ^ 2 - c) (hxy : M ∣ y - x) :
    M ∣ y ^ 2 - c := by
  rcases hx with ⟨u, hu⟩
  rcases hxy with ⟨v, hv⟩
  refine ⟨u + v * (y + x), ?_⟩
  calc
    y ^ 2 - c = (x ^ 2 - c) + (y - x) * (y + x) := by ring
    _ = M * u + (M * v) * (y + x) := by rw [hu, hv]
    _ = M * (u + v * (y + x)) := by ring

/-- For odd `M`, a square root of `c` modulo `M` has an even representative:
if `x` is odd, take `x + M`. No parity condition on `c` is needed. -/
theorem exists_even_square_root {M c x : ℤ}
    (hM : M % 2 = 1) (hx : M ∣ x ^ 2 - c) :
    ∃ y : ℤ, M ∣ y ^ 2 - c ∧ y % 2 = 0 := by
  by_cases heven : x % 2 = 0
  · exact ⟨x, hx, heven⟩
  have hxlo : 0 ≤ x % 2 := Int.emod_nonneg _ (by norm_num)
  have hxhi : x % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  have hodd : x % 2 = 1 := by omega
  refine ⟨x + M, square_root_dvd_of_congruent hx ?_, ?_⟩
  · exact ⟨1, by ring⟩
  · norm_num [Int.add_emod, hodd, hM]

/-- For odd `m`, a solution `A` of `9m ∣ A² + a - 3m` can be chosen even,
by adding `9m` if necessary. -/
theorem exists_even_123_strong_root {m a A : ℤ}
    (hm : m % 2 = 1)
    (hA : 9 * m ∣ A ^ 2 + a - 3 * m) :
    ∃ B : ℤ, (9 * m ∣ B ^ 2 + a - 3 * m) ∧ B % 2 = 0 := by
  have hmod : (9 * m) % 2 = 1 := by
    norm_num [Int.mul_emod, hm]
  have hroot : 9 * m ∣ A ^ 2 - (3 * m - a) := by
    convert hA using 1; ring
  obtain ⟨B, hB, hBeven⟩ := exists_even_square_root hmod hroot
  refine ⟨B, ?_, hBeven⟩
  convert hB using 1; ring

/-- If `m` is nonzero modulo the prime `p` and `-6m` is a square modulo `p`, then
`p ∣ 6 + mt²` for some integer `t`: take `t ≡ u/m`, where `u² ≡ -6m`. -/
theorem exists_123_binary_dvd_of_squareRootMod
    {p : ℕ} [Fact p.Prime] {m : ℤ}
    (hm : (m : ZMod p) ≠ 0)
    (hroot : HasSquareRootMod (-6 * m) p) :
    ∃ t : ℤ, (p : ℤ) ∣ 6 + m * t ^ 2 := by
  obtain ⟨u, hu⟩ := hroot
  let v : ZMod p := u * (m : ZMod p)⁻¹
  have hv : 6 + (m : ZMod p) * v ^ 2 = 0 := by
    dsimp [v]
    rw [mul_pow, hu]
    push_cast
    field_simp [hm]; ring
  obtain ⟨t, ht⟩ := ZMod.intCast_surjective v
  refine ⟨t, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, ht] using hv

/-- If `m` and `-6m` are nonzero modulo the prime `p` and `-6m` is a square
modulo `p`, then `p ∣ 6 + mt²` for some integer `t`. -/
theorem exists_123_binary_dvd_of_legendre
    {p : ℕ} [Fact p.Prime] {m : ℤ}
    (hm : (m : ZMod p) ≠ 0)
    (hdisc : ((-6 * m : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-6 * m) = 1) :
    ∃ t : ℤ, (p : ℤ) ∣ 6 + m * t ^ 2 := by
  apply exists_123_binary_dvd_of_squareRootMod hm
  obtain ⟨u, hu⟩ := (legendreSym.eq_one_iff p hdisc).mp hleg
  exact ⟨u, by simpa only [pow_two] using hu.symm⟩

/-- If an odd `p` divides `6 + 2m₁t²`, then so does `2p`, since the quotient
is even. -/
theorem twice_123_binary_dvd_of_odd {p m₁ t : ℤ}
    (hp : p % 2 = 1) (h : p ∣ 6 + (2 * m₁) * t ^ 2) :
    2 * p ∣ 6 + (2 * m₁) * t ^ 2 := by
  obtain ⟨q, hq⟩ := h
  have hmod := congrArg (fun x : ℤ => x % 2) hq
  have hqeven : q % 2 = 0 := by
    norm_num [Int.add_emod, Int.mul_emod, hp] at hmod
    omega
  obtain ⟨k, hk⟩ := Int.dvd_iff_emod_eq_zero.mpr hqeven
  refine ⟨k, ?_⟩
  rw [hq, hk]
  ring

/-- The binary completion for the coefficient `2p`: if `p` is an odd prime,
`2m₁` and `-6(2m₁)` are nonzero modulo `p`, and `-6(2m₁)` is a square modulo
`p`, then `2p ∣ 6 + 2m₁t²` for some integer `t`. -/
theorem exists_123_twice_binary_dvd_of_legendre
    {p : ℕ} [Fact p.Prime] {m₁ : ℤ}
    (hpodd : p % 2 = 1)
    (hm : ((2 * m₁ : ℤ) : ZMod p) ≠ 0)
    (hdisc : ((-6 * (2 * m₁) : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-6 * (2 * m₁)) = 1) :
    ∃ t : ℤ, 2 * (p : ℤ) ∣ 6 + (2 * m₁) * t ^ 2 := by
  obtain ⟨t, ht⟩ := exists_123_binary_dvd_of_legendre hm hdisc hleg
  exact ⟨t, twice_123_binary_dvd_of_odd (by exact_mod_cast hpodd) ht⟩

end FibonacciCriterion.Regular123SquareRoots
