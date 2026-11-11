import FibonacciCriterion.ClassicalInputs.Representation

/-!
# The obstruction for `⟨1,2,5⟩`

The form `x² + 2y² + 5z²` represents no integer `5 · 25^a · (5b + r)` with
`r = 2` or `r = 3` (`not_represents125_of_exceptional`). As in the manuscript,
the binary form `x² + 2y²` is anisotropic modulo 5, and the proof divides the
coordinates by 5, hence the value by 25.

The converse is the statement `Regular125Sufficiency`, which
`ClassicalInputs.Regular125.Classification` proves; `regular125_criterion_of_sufficiency`
combines the two directions.
-/

namespace FibonacciCriterion

open ClassicalRepresentation

/-- Every square is 0, 1, or 4 modulo 5. -/
theorem regular125_square_mod_five (x : ℤ) :
    x ^ 2 % 5 = 0 ∨ x ^ 2 % 5 = 1 ∨ x ^ 2 % 5 = 4 := by
  have hlo : 0 ≤ x % 5 := Int.emod_nonneg _ (by norm_num)
  have hhi : x % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  generalize hr : x % 5 = r at hlo hhi ⊢
  interval_cases r <;>
    norm_num [pow_two, Int.mul_emod, hr]

/-- No square is 2 or 3 modulo 5. -/
theorem regular125_square_mod_five_ne_two_three (x r : ℤ)
    (hr : r = 2 ∨ r = 3) : x ^ 2 % 5 ≠ r % 5 := by
  rcases regular125_square_mod_five x with hx | hx | hx <;>
    rcases hr with rfl | rfl <;> omega

/-- If `5 ∣ x² + 2y² + 5z²`, then 5 divides both `x` and `y`, since the
binary form `x² + 2y²` is anisotropic modulo 5. -/
theorem regular125_anisotropic_binary (x y z : ℤ)
    (h : (x ^ 2 + 2 * y ^ 2 + 5 * z ^ 2) % 5 = 0) :
    x % 5 = 0 ∧ y % 5 = 0 := by
  apply RegularReductions.dvd_five_of_sq_add_two_sq x y
  have hm := h
  norm_num [Int.add_emod, Int.mul_emod] at hm ⊢
  omega

/-- The descent step: if `x² + 2y² + 5z² = 5N`, then `x = 5X`, `y = 5Y`, and
`5X² + 10Y² + z² = N`. -/
theorem regular125_descent_step {x y z N : ℤ}
    (h : x ^ 2 + 2 * y ^ 2 + 5 * z ^ 2 = 5 * N) :
    ∃ X Y : ℤ, x = 5 * X ∧ y = 5 * Y ∧ 5 * X ^ 2 + 10 * Y ^ 2 + z ^ 2 = N := by
  have hmod : (x ^ 2 + 2 * y ^ 2 + 5 * z ^ 2) % 5 = 0 := by
    rw [h]
    norm_num [Int.mul_emod]
  obtain ⟨hx, hy⟩ := regular125_anisotropic_binary x y z hmod
  obtain ⟨X, rfl⟩ := Int.dvd_iff_emod_eq_zero.mpr hx
  obtain ⟨Y, rfl⟩ := Int.dvd_iff_emod_eq_zero.mpr hy
  exact ⟨X, Y, rfl, rfl, by nlinarith [h]⟩

/-- The case `a = 0`: `⟨1,2,5⟩` does not represent `5(5b + r)` with
`r = 2` or `r = 3`, an integer of 5-adic valuation 1 whose unit part is a
nonsquare modulo 5. -/
theorem not_represents125_five_nonsquare (b r : ℤ)
    (hr : r = 2 ∨ r = 3) :
    ¬ Represents125 (5 * (5 * b + r)) := by
  rintro ⟨x, y, z, hxyz⟩
  obtain ⟨X, Y, rfl, rfl, hdivfive⟩ := regular125_descent_step hxyz
  have hsq : z ^ 2 % 5 = r % 5 := by
    have hm := congrArg (fun t : ℤ => t % 5) hdivfive
    norm_num [Int.add_emod, Int.mul_emod] at hm ⊢
    omega
  exact regular125_square_mod_five_ne_two_three z r hr hsq

/-- The form `x² + 2y² + 5z²` represents no integer `5 · 25^a · (5b + r)`
with `r = 2` or `r = 3`. The proof is by induction on `a`: for `a ≥ 1` the
value is divisible by 25, which forces all three coordinates to be divisible
by 5. -/
theorem not_represents125_exceptional_family (a : ℕ) (b r : ℤ)
    (hr : r = 2 ∨ r = 3) :
    ¬ Represents125 (5 * 25 ^ a * (5 * b + r)) := by
  induction a with
  | zero =>
      simpa using not_represents125_five_nonsquare b r hr
  | succ a ih =>
      rintro ⟨x, y, z, hxyz⟩
      obtain ⟨X, Y, rfl, rfl, hdivfive⟩ :=
        regular125_descent_step (N := 25 ^ (a + 1) * (5 * b + r)) (by rw [hxyz]; ring)
      have hzsq : z ^ 2 % 5 = 0 := by
        have hm := congrArg (fun t : ℤ => t % 5) hdivfive
        norm_num [Int.add_emod, Int.mul_emod, pow_succ] at hm ⊢
        omega
      have hz : z % 5 = 0 := by
        have hzlo : 0 ≤ z % 5 := Int.emod_nonneg _ (by norm_num)
        have hzhi : z % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
        generalize hzr : z % 5 = zr at hzlo hzhi hzsq ⊢
        interval_cases zr <;>
          norm_num [pow_two, Int.mul_emod, hzr] at hzsq
        norm_num [hzr]
      have hzdiv : (5 : ℤ) ∣ z := Int.dvd_iff_emod_eq_zero.mpr hz
      obtain ⟨Z, rfl⟩ := hzdiv
      apply ih
      refine ⟨X, Y, Z, ?_⟩
      have hscaled :
          25 * (X ^ 2 + 2 * Y ^ 2 + 5 * Z ^ 2) =
            25 * (5 * 25 ^ a * (5 * b + r)) := by
        calc
          25 * (X ^ 2 + 2 * Y ^ 2 + 5 * Z ^ 2) =
              (5 * X) ^ 2 + 2 * (5 * Y) ^ 2 + 5 * (5 * Z) ^ 2 := by ring
          _ = 5 * 25 ^ (a + 1) * (5 * b + r) := hxyz
          _ = 25 * (5 * 25 ^ a * (5 * b + r)) := by
            rw [pow_succ]
            ring
      exact mul_left_cancel₀ (by norm_num : (25 : ℤ) ≠ 0) hscaled

/-- `⟨1,2,5⟩` represents no member of its exceptional set. -/
theorem not_represents125_of_exceptional (n : ℤ)
    (hn : Exceptional125 n) : ¬ Represents125 n := by
  rcases hn with ⟨a, b, r, hr, rfl⟩
  exact not_represents125_exceptional_family a b r hr

/-- Every integer represented by `⟨1,2,5⟩` lies outside its exceptional
set. -/
theorem not_exceptional125_of_represents (n : ℤ)
    (hn : Represents125 n) : ¬ Exceptional125 n := by
  intro hex
  exact not_represents125_of_exceptional n hex hn

/-- Sufficiency for `⟨1,2,5⟩`: every nonnegative integer outside the
exceptional set is represented. `ClassicalInputs.Regular125.Classification` proves it. -/
def Regular125Sufficiency : Prop :=
  ∀ n : ℤ, 0 ≤ n → ¬ Exceptional125 n → Represents125 n

/-- Given sufficiency, a nonnegative integer is represented by `⟨1,2,5⟩`
if and only if it lies outside the exceptional set. -/
theorem regular125_criterion_of_sufficiency
    (h : Regular125Sufficiency) (n : ℤ) (hn : 0 ≤ n) :
    Represents125 n ↔ ¬ Exceptional125 n := by
  constructor
  · exact not_exceptional125_of_represents n
  · exact h n hn

end FibonacciCriterion
