import FibonacciCriterion.Irregular.Forms

/-!
# The modulo-12 transfer from `h` to `f` (Lemma 3.4)

Lemma 3.4: a value of `f` or `h` that is not 7 or 10 modulo 12 is a value of
`f` (`representsF_of_representsH_of_mod_twelve`,
`representsF_of_class_of_mod_twelve`). As in the manuscript, the proof uses
the maps `B₂/2` and `B₃/3` of Table 3 on the coordinate classes where they are
integral; here each is an identity in parametrized coordinates, so no division
occurs. The choice of parity and signs is checked over `(ℤ/6)³`
(`mod_twelve_choice_checked`).
-/

namespace FibonacciCriterion.Irregular

/-- The map `B₂/2` with `a = 2t - c`: `f(-b, 2c, -t) = h(2t - c, b, c)`. -/
theorem f_parity_transfer_identity (b c t : ℤ) :
    f (-b) (2 * c) (-t) = h (2 * t - c) b c := by
  unfold f h
  ring

/-- The map `B₃/3` with `-a - b + c = 3t`:
`f(t + 2c, t + b, t - c) = h(c - b - 3t, b, c)`. -/
theorem f_mod_three_transfer_identity (b c t : ℤ) :
    f (t + 2 * c) (t + b) (t - c) = h (c - b - 3 * t) b c := by
  unfold f h
  ring

/-- If `a + c` is even, then `f` represents `h(a, b, c)`. -/
theorem representsF_of_h_even_sum (a b c : ℤ) (ha : 2 ∣ a + c) :
    RepresentsF (h a b c) := by
  obtain ⟨t, ht⟩ := ha
  have heq : a = 2 * t - c := by omega
  rw [heq]
  exact ⟨-b, 2 * c, -t, f_parity_transfer_identity b c t⟩

/-- If `b + c` is even, then `f` represents `h(a, b, c)`: exchange `a` and `b`
before applying `B₂/2`. -/
theorem representsF_of_h_even_sum_right (a b c : ℤ) (hb : 2 ∣ b + c) :
    RepresentsF (h a b c) := by
  have hr := representsF_of_h_even_sum b a c hb
  have heq : h b a c = h a b c := by
    unfold h
    ring
  rwa [heq] at hr

/-- If `3 ∣ -a - b + c`, then `f` represents `h(a, b, c)`, by `B₃/3`. -/
theorem representsF_of_h_three_relation (a b c : ℤ)
    (habc : 3 ∣ -a - b + c) : RepresentsF (h a b c) := by
  obtain ⟨t, ht⟩ := habc
  have heq : a = c - b - 3 * t := by omega
  rw [heq]
  exact ⟨t + 2 * c, t + b, t - c, f_mod_three_transfer_identity b c t⟩

/-- `h` is unchanged when the sign of its first coordinate changes. -/
theorem h_neg_left (a b c : ℤ) : h (-a) b c = h a b c := by
  unfold h
  ring

/-- `h` is unchanged when the sign of its second coordinate changes. -/
theorem h_neg_middle (a b c : ℤ) : h a (-b) c = h a b c := by
  unfold h
  ring

set_option maxRecDepth 100000 in
/-- The parity and sign choices of Lemma 3.4: if `a² + b² + 7c²` is not 7 or
10 modulo 12, then `a + c` or `b + c` is even, or `±a ± b + c` is divisible by
3 for some choice of signs. Checked on residues modulo 6. -/
theorem mod_twelve_choice_checked :
    ∀ a b c : Fin 6,
      ((a.val : ℤ) ^ 2 + (b.val : ℤ) ^ 2 + 7 * (c.val : ℤ) ^ 2) % 12 ≠ 7 →
      ((a.val : ℤ) ^ 2 + (b.val : ℤ) ^ 2 + 7 * (c.val : ℤ) ^ 2) % 12 ≠ 10 →
        ((a.val : ℤ) + c.val) % 2 = 0 ∨ ((b.val : ℤ) + c.val) % 2 = 0 ∨
        (-(a.val : ℤ) - b.val + c.val) % 3 = 0 ∨
        ((a.val : ℤ) - b.val + c.val) % 3 = 0 ∨
        (-(a.val : ℤ) + b.val + c.val) % 3 = 0 ∨
        ((a.val : ℤ) + b.val + c.val) % 3 = 0 := by
  decide +kernel

/-- Every integer is a residue in `[0, 6)` plus a multiple of 6. -/
theorem exists_fin_six (a : ℤ) : ∃ r : Fin 6, ∃ t : ℤ, a = (r.val : ℤ) + 6 * t :=
  ⟨⟨(a % 6).toNat, by omega⟩, a / 6, by
    have h0 : 0 ≤ a % 6 := Int.emod_nonneg _ (by norm_num)
    simp only [Int.toNat_of_nonneg h0]
    omega⟩

/-- Lemma 3.4 for `h`: a value of `h` that is not 7 or 10 modulo 12 is a value
of `f`. -/
theorem representsF_of_representsH_of_mod_twelve (n : ℤ) (hh : RepresentsH n)
    (h7 : n % 12 ≠ 7) (h10 : n % 12 ≠ 10) : RepresentsF n := by
  obtain ⟨a, b, c, rfl⟩ := hh
  obtain ⟨ra, ta, rfl⟩ := exists_fin_six a
  obtain ⟨rb, tb, rfl⟩ := exists_fin_six b
  obtain ⟨rc, tc, rfl⟩ := exists_fin_six c
  have hmod : h ((ra.val : ℤ) + 6 * ta) ((rb.val : ℤ) + 6 * tb) ((rc.val : ℤ) + 6 * tc) % 12 =
      ((ra.val : ℤ) ^ 2 + (rb.val : ℤ) ^ 2 + 7 * (rc.val : ℤ) ^ 2) % 12 := by
    have hexp : h ((ra.val : ℤ) + 6 * ta) ((rb.val : ℤ) + 6 * tb) ((rc.val : ℤ) + 6 * tc) =
        ((ra.val : ℤ) ^ 2 + (rb.val : ℤ) ^ 2 + 7 * (rc.val : ℤ) ^ 2) +
          12 * ((ra.val : ℤ) * ta + 3 * ta ^ 2 + (rb.val : ℤ) * tb + 3 * tb ^ 2 +
            7 * (rc.val : ℤ) * tc + 21 * tc ^ 2) := by
      unfold h
      ring
    rw [hexp, Int.add_mul_emod_self_left]
  rw [hmod] at h7 h10
  rcases mod_twelve_choice_checked ra rb rc h7 h10 with hp | hp | hp | hp | hp | hp
  · exact representsF_of_h_even_sum _ _ _ (Int.dvd_of_emod_eq_zero (by omega))
  · exact representsF_of_h_even_sum_right _ _ _ (Int.dvd_of_emod_eq_zero (by omega))
  · exact representsF_of_h_three_relation _ _ _ (Int.dvd_of_emod_eq_zero (by omega))
  · rw [← h_neg_left]
    exact representsF_of_h_three_relation _ _ _ (Int.dvd_of_emod_eq_zero (by omega))
  · rw [← h_neg_middle]
    exact representsF_of_h_three_relation _ _ _ (Int.dvd_of_emod_eq_zero (by omega))
  · rw [← h_neg_left, ← h_neg_middle]
    exact representsF_of_h_three_relation _ _ _ (Int.dvd_of_emod_eq_zero (by omega))

/-- Lemma 3.4: a value of `f` or `h` that is not 7 or 10 modulo 12 is a value
of `f`. -/
theorem representsF_of_class_of_mod_twelve (n : ℤ)
    (hn : RepresentsF n ∨ RepresentsH n) (h7 : n % 12 ≠ 7) (h10 : n % 12 ≠ 10) :
    RepresentsF n := by
  rcases hn with hf | hh
  · exact hf
  · exact representsF_of_representsH_of_mod_twelve n hh h7 h10

end FibonacciCriterion.Irregular
