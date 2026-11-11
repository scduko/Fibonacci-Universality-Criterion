import FibonacciCriterion.ClassicalInputs.DeterminantSeven.Classes

/-!
# The number of zeros modulo 7

Modulo 7, the classes of `f` and `h` have an anisotropic nonsingular
binary quotient, and the third class of determinant 7 has a split one.
Here this distinction is the number of zeros on `(ZMod 7)³` of the form taken
modulo 7 (`modSevenZeroCount`): seven for `f` and `h`, and 91 for the third
class. Lean does not state these two values; it checks that a matrix of
`reducedDetSeven` with seven zeros is one of the three matrices of
`reducedFHGenus` (`mem_reducedFHGenus_of_mem_reducedDetSeven_of_zeroCount`). A
value-preserving bijection of `(ZMod 7)³` keeps the count
(`modSevenZeroCount_eq_of_isometry`).

The manuscript's residue invariant is the square class of the determinant of
the binary quotient; the zero count replaces it. The count is a finite
computation; no lattice reduction enters.
-/

namespace FibonacciCriterion.TernaryGram

/-- The form of `A`, reduced modulo 7, evaluated at a vector of
`(ZMod 7)³`. -/
def evalModSeven (A : TernaryGram) (v : Fin 3 → ZMod 7) : ZMod 7 :=
  (A.a : ZMod 7) * v 0 ^ 2 + (A.b : ZMod 7) * v 1 ^ 2 +
    (A.c : ZMod 7) * v 2 ^ 2 +
    2 * (A.r : ZMod 7) * v 0 * v 1 +
    2 * (A.s : ZMod 7) * v 0 * v 2 +
    2 * (A.t : ZMod 7) * v 1 * v 2

end FibonacciCriterion.TernaryGram

namespace FibonacciCriterion.DeterminantSevenGenus

/-- The zeros in `(ZMod 7)³` of the form of `A` reduced modulo 7. -/
def modSevenZeros (A : TernaryGram) : Finset (Fin 3 → ZMod 7) :=
  Finset.univ.filter fun v ↦ A.evalModSeven v = 0

/-- The number of zeros in `(ZMod 7)³` of the form of `A` reduced modulo
7. -/
def modSevenZeroCount (A : TernaryGram) : ℕ := (modSevenZeros A).card

/-- A bijection `e` of `(ZMod 7)³` with `A(e v) = B(v)` for the forms reduced
modulo 7. Linearity is not required, since the zero count does not need
it. -/
structure ModSevenIsometry (A B : TernaryGram) where
  /-- The bijection `e` of `(ZMod 7)³`. -/
  toEquiv : (Fin 3 → ZMod 7) ≃ (Fin 3 → ZMod 7)
  map_eval : ∀ v, A.evalModSeven (toEquiv v) = B.evalModSeven v

/-- Forms related by a `ModSevenIsometry` have the same number of zeros
modulo 7. -/
theorem modSevenZeroCount_eq_of_isometry {A B : TernaryGram}
    (e : ModSevenIsometry A B) :
    modSevenZeroCount A = modSevenZeroCount B := by
  let forward : {v // v ∈ modSevenZeros B} → {v // v ∈ modSevenZeros A} :=
    fun v => Subtype.mk (e.toEquiv v.val) (by
      simp only [modSevenZeros, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [e.map_eval v.val]
      simpa only [modSevenZeros, Finset.mem_filter, Finset.mem_univ, true_and]
        using v.property)
  let backward : {v // v ∈ modSevenZeros A} → {v // v ∈ modSevenZeros B} :=
    fun w => Subtype.mk (e.toEquiv.symm w.val) (by
      simp only [modSevenZeros, Finset.mem_filter, Finset.mem_univ, true_and]
      have hw : A.evalModSeven w.val = 0 := by
        simpa only [modSevenZeros, Finset.mem_filter, Finset.mem_univ, true_and]
          using w.property
      have he := e.map_eval (e.toEquiv.symm w.val)
      simp only [Equiv.apply_symm_apply] at he
      rw [← he]
      exact hw)
  let E : {v // v ∈ modSevenZeros B} ≃ {v // v ∈ modSevenZeros A} :=
    { toFun := forward
      invFun := backward
      left_inv := by
        intro v
        apply Subtype.ext
        change e.toEquiv.symm (e.toEquiv v.val) = v.val
        exact e.toEquiv.symm_apply_apply v.val
      right_inv := by
        intro w
        apply Subtype.ext
        change e.toEquiv (e.toEquiv.symm w.val) = w.val
        exact e.toEquiv.apply_symm_apply w.val }
  have hcard := Fintype.card_congr E
  simpa [modSevenZeroCount] using hcard.symm

/-! ## The zero count of the reduced matrices -/

/-- The check that every matrix of `reducedDetSeven` with seven zeros modulo
7 lies in `reducedFHGenus`. -/
def reducedDetSevenZeroCountCheck : Bool :=
  reducedDetSeven.all fun A ↦
    decide (modSevenZeroCount A = 7 → A ∈ reducedFHGenus)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The kernel check of `reducedDetSevenZeroCountCheck`: fifteen
matrices, each evaluated at the 343 vectors of `(ZMod 7)³`. -/
theorem reducedDetSevenZeroCountCheck_eq_true :
    reducedDetSevenZeroCountCheck = true := by
  decide

/-- A matrix of `reducedDetSeven` with seven zeros modulo 7 lies in
`reducedFHGenus`: the zero count excludes the twelve matrices of the third
class. -/
theorem mem_reducedFHGenus_of_mem_reducedDetSeven_of_zeroCount
    (A : TernaryGram) (hA : A ∈ reducedDetSeven)
    (hzero : modSevenZeroCount A = 7) :
    A ∈ reducedFHGenus := by
  have hall : ∀ B ∈ reducedDetSeven,
      modSevenZeroCount B = 7 → B ∈ reducedFHGenus := by
    simpa only [reducedDetSevenZeroCountCheck, List.all_eq_true,
      decide_eq_true_eq] using reducedDetSevenZeroCountCheck_eq_true
  exact hall A hA hzero

end FibonacciCriterion.DeterminantSevenGenus
