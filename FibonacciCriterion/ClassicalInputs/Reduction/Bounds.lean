import Mathlib.Tactic

/-!
# Integer inequalities for Mahler's bound

The polynomial inequalities behind Mahler's bound `abc ≤ 2D` for a
Minkowski-reduced positive-definite ternary Gram matrix of determinant `D`
(`two_mul_abc_le_four_det_of_sign_sums`), and the ranges
`a ≤ 2`, `b ≤ 4` that the bound gives for `D ≤ 10` (`small_diagonal_ranges`).
The statements involve integers only; `ClassicalInputs.Reduction.ReducedGram` applies them to
Gram matrices. The manuscript cites Mahler for the bound; here it is proven.
-/

namespace FibonacciCriterion.TernaryReductionBounds

/-- The reduction inequalities in the acute chamber: `0 < a ≤ b`,
`0 ≤ X ≤ a`, `0 ≤ Y ≤ a`, and `0 ≤ Z ≤ b`, where `X, Y, Z` are the doubled
off-diagonal coefficients. -/
def AcuteReducedBounds (a b X Y Z : ℤ) : Prop :=
  0 < a ∧ a ≤ b ∧
    0 ≤ X ∧ X ≤ a ∧ 0 ≤ Y ∧ Y ≤ a ∧ 0 ≤ Z ∧ Z ≤ b

/-- The error estimate for Mahler's bound in the acute chamber, where the
doubled off-diagonal coefficients `X, Y, Z` are nonnegative:
`aZ² + bY² + bX² - XYZ ≤ 2ab²`. The obtuse chamber, which needs the extra
inequality `a + b + X + Y + Z ≥ 0`, is `obtuse_mixed_error_le`. -/
theorem acute_mixed_error_le (a b X Y Z : ℤ)
    (h : AcuteReducedBounds a b X Y Z) :
    a * Z ^ 2 + b * Y ^ 2 + b * X ^ 2 - X * Y * Z ≤ 2 * a * b ^ 2 := by
  rcases h with ⟨ha, hab, hX0, hXa, hY0, hYa, hZ0, hZb⟩
  have hXsq : X ^ 2 ≤ a * X := by nlinarith [mul_nonneg hX0 (sub_nonneg.mpr hXa)]
  have hYsq : Y ^ 2 ≤ a * Y := by nlinarith [mul_nonneg hY0 (sub_nonneg.mpr hYa)]
  have hZsq : Z ^ 2 ≤ b * Z := by nlinarith [mul_nonneg hZ0 (sub_nonneg.mpr hZb)]
  have hYZ : Y * Z ≤ a * b :=
    mul_le_mul hYa hZb hZ0 (le_trans hY0 hYa)
  have hstepX :
      a * b * (X + Y + Z) - X * Y * Z ≤
        a * b * (a + Y + Z) - a * Y * Z := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hXa) (sub_nonneg.mpr hYZ)]
  have hstepY :
      a * b * (a + Y + Z) - a * Y * Z ≤
        a * b * (a + a + Z) - a * a * Z := by
    have : 0 ≤ a * (b - Z) := mul_nonneg ha.le (sub_nonneg.mpr hZb)
    nlinarith [mul_nonneg (sub_nonneg.mpr hYa) this]
  have hstepZ :
      a * b * (a + a + Z) - a * a * Z ≤ 2 * a * b ^ 2 := by
    have : 0 ≤ a * (b - a) := mul_nonneg ha.le (sub_nonneg.mpr hab)
    nlinarith [mul_nonneg (sub_nonneg.mpr hZb) this]
  calc
    a * Z ^ 2 + b * Y ^ 2 + b * X ^ 2 - X * Y * Z
        ≤ a * b * (X + Y + Z) - X * Y * Z := by nlinarith
    _ ≤ a * b * (a + Y + Z) - a * Y * Z := hstepX
    _ ≤ a * b * (a + a + Z) - a * a * Z := hstepY
    _ ≤ 2 * a * b ^ 2 := hstepZ

/-- The same estimate in the obtuse chamber, where `R, S, T` are the
negatives of the doubled off-diagonal coefficients. The last hypothesis comes
from the reduction inequality `N(b₂) ≤ N(b₀ + b₁ + b₂)`. -/
theorem obtuse_mixed_error_le (a b R S T : ℤ)
    (ha : 0 < a) (hab : a ≤ b)
    (hR0 : 0 ≤ R) (hRa : R ≤ a)
    (hS0 : 0 ≤ S) (hSa : S ≤ a)
    (hT0 : 0 ≤ T) (hTb : T ≤ b)
    (hsum : R + S + T ≤ a + b) :
    R * S * T + a * T ^ 2 + b * S ^ 2 + b * R ^ 2 ≤ 2 * a * b ^ 2 := by
  have hb0 : 0 ≤ b := le_trans ha.le hab
  have htwo : 0 ≤ 2 * b - T := by linarith
  have hgroup :
      R * S * T + b * S ^ 2 + b * R ^ 2 ≤ b * (R + S) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hR0 hS0) htwo]
  by_cases hsmall : R + S ≤ a
  · have hU0 : 0 ≤ R + S := add_nonneg hR0 hS0
    have hUsq := mul_self_le_mul_self hU0 hsmall
    have hTsq := mul_self_le_mul_self hT0 hTb
    have haab : a ^ 2 ≤ a * b := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hab)]
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hUsq),
      mul_nonneg ha.le (sub_nonneg.mpr hTsq)]
  · have hlarge : a ≤ R + S := by omega
    set V : ℤ := R + S - a
    have hV0 : 0 ≤ V := sub_nonneg.mpr hlarge
    have hVa : V ≤ a := by dsimp [V]; linarith
    have hTV : T ≤ b - V := by dsimp [V]; linarith
    have hRS : a * V ≤ R * S := by
      have hp := mul_nonneg (sub_nonneg.mpr hRa) (sub_nonneg.mpr hSa)
      dsimp [V]
      nlinarith
    have hreplace :
        R * S * (T - 2 * b) ≤ a * V * (T - 2 * b) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hRS) htwo]
    have hfirst :
        R * S * T + b * S ^ 2 + b * R ^ 2 ≤
          b * (R + S) ^ 2 + a * V * (T - 2 * b) := by
      have hid :
          R * S * T + b * S ^ 2 + b * R ^ 2 =
            b * (R + S) ^ 2 + R * S * (T - 2 * b) := by ring
      rw [hid]
      nlinarith [hreplace]
    have hendpoint :
        b * (R + S) ^ 2 + a * V * (T - 2 * b) + a * T ^ 2 ≤
          a * b ^ 2 + b * (a ^ 2 + V ^ 2 - a * V) := by
      have hgap : 0 ≤ b - V - T := by linarith
      have hbt : 0 ≤ b + T := add_nonneg hb0 hT0
      have hp := mul_nonneg (mul_nonneg ha.le hgap) hbt
      dsimp [V] at hp ⊢
      nlinarith
    have hquad : a ^ 2 + V ^ 2 - a * V ≤ a * b := by
      have hp := mul_nonneg hV0 (sub_nonneg.mpr hVa)
      have habp := mul_nonneg ha.le (sub_nonneg.mpr hab)
      nlinarith
    have hbmul := mul_le_mul_of_nonneg_left hquad hb0
    nlinarith

/-- Mahler's bound in doubled form, `2abc ≤ 4abc + XYZ - aZ² - bY² - cX²`, in
a weak sign chamber: `X, Y, Z ≥ 0`, or `X, Y, Z ≤ 0` with
`a + b + X + Y + Z ≥ 0`. With `X = 2r`, `Y = 2s`, `Z = 2t`, the right side is
`4 det`. Weak inequalities make the eight-case split of the next lemma
uniform. -/
theorem two_mul_abc_le_four_det_of_weak_chamber
    (a b c X Y Z : ℤ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hXa : |X| ≤ a) (hYa : |Y| ≤ a) (hZb : |Z| ≤ b)
    (hsign : (0 ≤ X ∧ 0 ≤ Y ∧ 0 ≤ Z) ∨
      (X ≤ 0 ∧ Y ≤ 0 ∧ Z ≤ 0 ∧ 0 ≤ a + b + X + Y + Z)) :
    2 * a * b * c ≤ 4 * a * b * c + X * Y * Z -
      a * Z ^ 2 - b * Y ^ 2 - c * X ^ 2 := by
  have hX0 : 0 ≤ |X| := abs_nonneg X
  have hXsq : X ^ 2 ≤ a ^ 2 := by
    have hxMul := mul_self_le_mul_self hX0 hXa
    have hxPow : |X| ^ 2 ≤ a ^ 2 := by simpa [pow_two] using hxMul
    simpa only [sq_abs] using hxPow
  have haa : a ^ 2 ≤ 2 * a * b := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hab)]
  have htail : (c - b) * X ^ 2 ≤ (c - b) * (2 * a * b) :=
    mul_le_mul_of_nonneg_left (hXsq.trans haa) (sub_nonneg.mpr hbc)
  rcases hsign with hpos | hneg
  · rcases hpos with ⟨hX, hY, hZ⟩
    have herr := acute_mixed_error_le a b X Y Z
      ⟨ha, hab, hX, (le_abs_self X).trans hXa,
        hY, (le_abs_self Y).trans hYa, hZ, (le_abs_self Z).trans hZb⟩
    nlinarith
  · rcases hneg with ⟨hX, hY, hZ, hsum⟩
    have herr := obtuse_mixed_error_le a b (-X) (-Y) (-Z) ha hab
      (neg_nonneg.mpr hX) (by simpa [abs_of_nonpos hX] using hXa)
      (neg_nonneg.mpr hY) (by simpa [abs_of_nonpos hY] using hYa)
      (neg_nonneg.mpr hZ) (by simpa [abs_of_nonpos hZ] using hZb)
      (by linarith)
    nlinarith

/-- Mahler's bound in doubled form for arbitrary signs of `X, Y, Z`, given the
four sign-sum inequalities. Each of the eight sign cases reduces to a weak
chamber by changing an even number of signs, which leaves `XYZ` and the three
squares unchanged. -/
theorem two_mul_abc_le_four_det_of_sign_sums
    (a b c X Y Z : ℤ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hXa : |X| ≤ a) (hYa : |Y| ≤ a) (hZb : |Z| ≤ b)
    (h₁ : 0 ≤ a + b + X + Y + Z)
    (h₂ : 0 ≤ a + b + X - Y - Z)
    (h₃ : 0 ≤ a + b - X + Y - Z)
    (h₄ : 0 ≤ a + b - X - Y + Z) :
    2 * a * b * c ≤ 4 * a * b * c + X * Y * Z -
      a * Z ^ 2 - b * Y ^ 2 - c * X ^ 2 := by
  by_cases hX : 0 ≤ X <;> by_cases hY : 0 ≤ Y <;> by_cases hZ : 0 ≤ Z
  · exact two_mul_abc_le_four_det_of_weak_chamber
      a b c X Y Z ha hab hbc hXa hYa hZb (Or.inl ⟨hX, hY, hZ⟩)
  · have h := two_mul_abc_le_four_det_of_weak_chamber
      a b c (-X) (-Y) Z ha hab hbc (by simpa) (by simpa) hZb
      (Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩)
    simpa [pow_two] using h
  · have h := two_mul_abc_le_four_det_of_weak_chamber
      a b c (-X) Y (-Z) ha hab hbc (by simpa) hYa (by simpa)
      (Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩)
    simpa [pow_two] using h
  · have h := two_mul_abc_le_four_det_of_weak_chamber
      a b c X (-Y) (-Z) ha hab hbc hXa (by simpa) (by simpa)
      (Or.inl ⟨hX, by linarith, by linarith⟩)
    simpa [pow_two] using h
  · have h := two_mul_abc_le_four_det_of_weak_chamber
      a b c X (-Y) (-Z) ha hab hbc hXa (by simpa) (by simpa)
      (Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩)
    simpa [pow_two] using h
  · have h := two_mul_abc_le_four_det_of_weak_chamber
      a b c (-X) Y (-Z) ha hab hbc (by simpa) hYa (by simpa)
      (Or.inl ⟨by linarith, hY, by linarith⟩)
    simpa [pow_two] using h
  · have h := two_mul_abc_le_four_det_of_weak_chamber
      a b c (-X) (-Y) Z ha hab hbc (by simpa) (by simpa) hZb
      (Or.inl ⟨by linarith, by linarith, hZ⟩)
    simpa [pow_two] using h
  · exact two_mul_abc_le_four_det_of_weak_chamber
      a b c X Y Z ha hab hbc hXa hYa hZb
      (Or.inr ⟨by linarith, by linarith, by linarith, h₁⟩)

/-- If `0 < a ≤ b`, `D ≤ 10`, and `2ab² ≤ 4D`, then `a ≤ 2` and `b ≤ 4`. The
hypothesis `2ab² ≤ 4D` follows from `b ≤ c` and Mahler's bound `abc ≤ 2D`. -/
theorem small_diagonal_ranges (a b D : ℤ)
    (ha : 0 < a) (hab : a ≤ b) (hD : D ≤ 10)
    (hsize : 2 * a * b ^ 2 ≤ 4 * D) : a ≤ 2 ∧ b ≤ 4 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hb_sq : b ≤ b ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ b by omega) (show 0 ≤ b - 1 by omega)]
  have hdropa : 2 * b ^ 2 ≤ 2 * a * b ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ a - 1 by omega) (sq_nonneg b)]
  have hb20 : b ≤ 20 := by nlinarith
  have hb4 : b ≤ 4 := by
    interval_cases b <;> norm_num at hsize ⊢ <;> nlinarith
  have habsq : a ^ 2 ≤ b ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (add_nonneg ha.le hb.le)]
  have hacube : 2 * a ^ 3 ≤ 2 * a * b ^ 2 := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr habsq)]
  have ha4 : a ≤ 4 := hab.trans hb4
  have ha2 : a ≤ 2 := by
    interval_cases a <;> norm_num at hacube hsize ⊢ <;> nlinarith
  exact ⟨ha2, hb4⟩

end FibonacciCriterion.TernaryReductionBounds
