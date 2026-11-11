import FibonacciCriterion.Irregular.Forms

/-!
# The square-transfer matrices (Table 3)

`transfer2`, …, `transfer109` are the twelve integral matrices `B_p` of
Table 3, for `p = 2, 3` and for the ten primes of `P₇`. Each
satisfies identity (8), `f(B_p v) = p² h(v)`, checked by `ring`. The
matrices for 2 and 3 give the maps of Lemma 3.4, which `Irregular.ModTwelve`
writes in divided form, `B₂/2` and `B₃/3`. `representsF_of_mem_transferPrimes`
turns a representation of `n` by `f` or `h` into a representation of `p² n`
by `f`. The period column of Table 3 is not reproduced:
`Irregular.RestrictedCover` checks a common return time for each group of
Lemma 6.6.
-/

namespace FibonacciCriterion.Irregular

/-- The matrix `B₂` of Table 3, listed by rows. -/
def transfer2 : TernaryLinearMap :=
  ⟨0, -2, 0, 0, 0, 4, -1, 0, -1⟩

/-- Identity (8) for `p = 2`. -/
theorem transfer2_spec : IsSquareTransfer 2 transfer2 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer2]
  ring

/-- The matrix `B₃` of Table 3, listed by rows. -/
def transfer3 : TernaryLinearMap :=
  ⟨-1, -1, 7, -1, 2, 1, -1, -1, -2⟩

/-- Identity (8) for `p = 3`. -/
theorem transfer3_spec : IsSquareTransfer 3 transfer3 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer3]
  ring

/-- The matrix `B₅` of Table 3, listed by rows. -/
def transfer5 : TernaryLinearMap :=
  ⟨-3, -3, 7, -2, 3, 3, -1, -1, -6⟩

/-- Identity (8) for `p = 5`. -/
theorem transfer5_spec : IsSquareTransfer 5 transfer5 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer5]
  ring

/-- The matrix `B₁₁` of Table 3, listed by rows. -/
def transfer11 : TernaryLinearMap :=
  ⟨-3, -7, -21, -1, -6, 15, -5, 3, -2⟩

/-- Identity (8) for `p = 11`. -/
theorem transfer11_spec : IsSquareTransfer 11 transfer11 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer11]
  ring

/-- The matrix `B₁₃` of Table 3, listed by rows. -/
def transfer13 : TernaryLinearMap :=
  ⟨-5, -9, -21, -6, -3, 19, -3, 5, -10⟩

/-- Identity (8) for `p = 13`. -/
theorem transfer13_spec : IsSquareTransfer 13 transfer13 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer13]
  ring

/-- The matrix `B₁₇` of Table 3, listed by rows. -/
def transfer17 : TernaryLinearMap :=
  ⟨-1, -15, -21, -3, 6, -29, 9, -1, 2⟩

/-- Identity (8) for `p = 17`. -/
theorem transfer17_spec : IsSquareTransfer 17 transfer17 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer17]
  ring

/-- The matrix `B₁₉` of Table 3, listed by rows. -/
def transfer19 : TernaryLinearMap :=
  ⟨-3, -3, 49, -6, 13, 3, -7, -7, -6⟩

/-- Identity (8) for `p = 19`. -/
theorem transfer19_spec : IsSquareTransfer 19 transfer19 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer19]
  ring

/-- The matrix `B₃₁` of Table 3, listed by rows. -/
def transfer31 : TernaryLinearMap :=
  ⟨-15, -13, 63, -2, 21, 27, -13, -3, -26⟩

/-- Identity (8) for `p = 31`. -/
theorem transfer31_spec : IsSquareTransfer 31 transfer31 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer31]
  ring

/-- The matrix `B₅₃` of Table 3, listed by rows. -/
def transfer53 : TernaryLinearMap :=
  ⟨-21, -39, 77, -14, 27, 69, -19, -5, -54⟩

/-- Identity (8) for `p = 53`. -/
theorem transfer53_spec : IsSquareTransfer 53 transfer53 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer53]
  ring

/-- The matrix `B₈₃` of Table 3, listed by rows. -/
def transfer83 : TernaryLinearMap :=
  ⟨-9, -9, 217, -26, 57, 9, -31, -31, -18⟩

/-- Identity (8) for `p = 83`. -/
theorem transfer83_spec : IsSquareTransfer 83 transfer83 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer83]
  ring

/-- The matrix `B₁₀₇` of Table 3, listed by rows. -/
def transfer107 : TernaryLinearMap :=
  ⟨-35, -51, -231, -30, -59, 123, -39, 41, -22⟩

/-- Identity (8) for `p = 107`. -/
theorem transfer107_spec : IsSquareTransfer 107 transfer107 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer107]
  ring

/-- The matrix `B₁₀₉` of Table 3, listed by rows. -/
def transfer109 : TernaryLinearMap :=
  ⟨-3, -105, -77, -41, -18, 183, -37, 13, -114⟩

/-- Identity (8) for `p = 109`. -/
theorem transfer109_spec : IsSquareTransfer 109 transfer109 := by
  intro x y z
  dsimp [f, h, TernaryLinearMap.x, TernaryLinearMap.y,
    TernaryLinearMap.z, transfer109]
  ring

/-- The twelve primes of Table 3: 2, 3, and the ten primes of `P₇`. -/
def transferPrimes : List ℤ :=
  [2, 3, 5, 11, 13, 17, 19, 31, 53, 83, 107, 109]

/-- Every `p` in `transferPrimes` has a square transfer: an integral matrix
`B` with `f(Bv) = p² h(v)`. -/
theorem exists_squareTransfer_of_mem {p : ℤ} (hp : p ∈ transferPrimes) :
    ∃ B : TernaryLinearMap, IsSquareTransfer p B := by
  simp only [transferPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨transfer2, transfer2_spec⟩
  · exact ⟨transfer3, transfer3_spec⟩
  · exact ⟨transfer5, transfer5_spec⟩
  · exact ⟨transfer11, transfer11_spec⟩
  · exact ⟨transfer13, transfer13_spec⟩
  · exact ⟨transfer17, transfer17_spec⟩
  · exact ⟨transfer19, transfer19_spec⟩
  · exact ⟨transfer31, transfer31_spec⟩
  · exact ⟨transfer53, transfer53_spec⟩
  · exact ⟨transfer83, transfer83_spec⟩
  · exact ⟨transfer107, transfer107_spec⟩
  · exact ⟨transfer109, transfer109_spec⟩

/-- For `p` in `transferPrimes`, if `f` or `h` represents `n`, then `f`
represents `p² n`. -/
theorem representsF_of_mem_transferPrimes {p n : ℤ}
    (hp : p ∈ transferPrimes) (hn : RepresentsF n ∨ RepresentsH n) :
    RepresentsF (p ^ 2 * n) := by
  obtain ⟨B, hB⟩ := exists_squareTransfer_of_mem hp
  exact representsF_of_either_class hB hn

end FibonacciCriterion.Irregular
