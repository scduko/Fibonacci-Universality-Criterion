import FibonacciCriterion.ClassicalInputs.ThreeSquares.Reductions

/-!
# The forms `⟨1,2,2⟩` and `⟨1,2,4⟩`

As in Proposition 3.2, `⟨1,2,2⟩` and `⟨1,1,1⟩` represent the same integers
(`represents122_iff_threeSquares`); `⟨1,2,4⟩` represents `2n` if and only if
`⟨1,2,2⟩` represents `n`; and at odd values `⟨1,2,4⟩` and `⟨1,1,2⟩` represent
the same integers. The proofs are identities and parity arguments and do not
use the three-square theorem. `Regular.TwoAdicEscalators` combines these
reductions with the three-square theorem to obtain the criteria for `⟨1,2,2⟩`
and `⟨1,2,4⟩`.
-/

namespace FibonacciCriterion.RegularReductions

/-- Representation of `n` by the diagonal form `⟨1,2,2⟩`. -/
def Represents122 (n : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + 2 * y ^ 2 + 2 * z ^ 2 = n

/-- Representation of `n` by the diagonal form `⟨1,2,4⟩`. -/
def Represents124 (n : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + 2 * y ^ 2 + 4 * z ^ 2 = n

/-- If `a² + b² + c² = n` with `a ≡ b (mod 2)`, then `⟨1,2,2⟩` represents `n`
at `(c, (a + b)/2, (a - b)/2)`. -/
theorem represents122_of_parity (n a b c : ℤ)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = n) (hab : a % 2 = b % 2) :
    Represents122 n := by
  have ha : a = (a + b) / 2 + (a - b) / 2 := by omega
  have hb : b = (a + b) / 2 - (a - b) / 2 := by omega
  refine ⟨c, (a + b) / 2, (a - b) / 2, ?_⟩
  nlinarith [congrArg (fun t : ℤ => t ^ 2) ha,
    congrArg (fun t : ℤ => t ^ 2) hb]

/-- The forms `⟨1,2,2⟩` and `⟨1,1,1⟩` represent the same integers. -/
theorem represents122_iff_threeSquares (n : ℤ) :
    Represents122 n ↔ ThreeSquares n := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨x, y + z, y - z, by nlinarith⟩
  · rintro ⟨x, y, z, h⟩
    have hp : x % 2 = y % 2 ∨ x % 2 = z % 2 ∨ y % 2 = z % 2 := by omega
    rcases hp with hxy | hxz | hyz
    · exact represents122_of_parity n x y z h hxy
    · exact represents122_of_parity n x z y (by nlinarith) hxz
    · exact represents122_of_parity n y z x (by nlinarith) hyz

/-- `⟨1,2,4⟩` represents `2n` if and only if `⟨1,2,2⟩` represents `n`. -/
theorem represents124_twice_iff (n : ℤ) :
    Represents124 (2 * n) ↔ Represents122 n := by
  constructor
  · rintro ⟨x, y, z, h⟩
    have hx : x % 2 = 0 := by
      have hx' : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hx' with hx' | hx'
      · exact hx'
      · have hm := congrArg (fun t : ℤ => t % 2) h
        norm_num [Int.add_emod, Int.mul_emod, pow_two, hx'] at hm
    have hdiv : x = 2 * (x / 2) := by omega
    exact ⟨y, x / 2, z, by nlinarith [congrArg (fun t : ℤ => t ^ 2) hdiv]⟩
  · rintro ⟨x, y, z, h⟩
    exact ⟨2 * y, x, z, by nlinarith⟩

/-- For odd `n`, `⟨1,2,4⟩` represents `n` if and only if `⟨1,1,2⟩` does: in a
representation `n = x² + y² + 2z²`, one of `x` and `y` is even. -/
theorem represents124_iff_represents112_of_odd (n : ℤ) (hn : n % 2 = 1) :
    Represents124 n ↔ Represents112 n := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨x, 2 * z, y, by nlinarith⟩
  · rintro ⟨x, y, z, h⟩
    have hp : x % 2 = 0 ∨ y % 2 = 0 := by
      by_contra hbad
      have hx : x % 2 = 1 := by omega
      have hy : y % 2 = 1 := by omega
      have hm := congrArg (fun t : ℤ => t % 2) h
      norm_num [Int.add_emod, Int.mul_emod, pow_two, hx, hy, hn] at hm
    rcases hp with hx | hy
    · have hdiv : x = 2 * (x / 2) := by omega
      exact ⟨y, z, x / 2, by nlinarith [congrArg (fun t : ℤ => t ^ 2) hdiv]⟩
    · have hdiv : y = 2 * (y / 2) := by omega
      exact ⟨x, z, y / 2, by nlinarith [congrArg (fun t : ℤ => t ^ 2) hdiv]⟩

end FibonacciCriterion.RegularReductions
