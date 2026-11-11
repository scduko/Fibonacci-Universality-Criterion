import FibonacciCriterion.Criterion.TableOne

/-!
# The congruence checks of Table 1

The residue checks in `Criterion.TableOne` show that each escalator `P_t` of Table 1
omits its truant `t` (`tableOneRow_polynomial_omits`). The checks use squares of
natural numbers modulo `m_t`; the proof passes from an integer coordinate to
its absolute value, which has the same square.
-/

namespace FibonacciCriterion

/-- The residue of every square modulo `m` lies in `squareResidues m`. -/
theorem square_mod_mem (m a : ℕ) (hm : 0 < m) :
    a ^ 2 % m ∈ squareResidues m := by
  simp only [squareResidues, List.mem_eraseDups, List.mem_map]
  refine ⟨a % m, List.mem_range.mpr (Nat.mod_lt a hm), ?_⟩
  simp only [pow_two, Nat.mul_mod, Nat.mod_mod]

namespace TableOneRow

/-- If the check succeeds, the diagonal form `α x² + β y² + γ z²` does not take
the value `scale · t` at natural numbers `x`, `y`, `z`. -/
theorem diagonal_obstruction_nat (p : TableOneRow)
    (h : p.checkObstruction = true) (x y z : ℕ) :
    p.obstructionCoefficients.1 * x ^ 2 +
      p.obstructionCoefficients.2.1 * y ^ 2 +
      p.obstructionCoefficients.2.2 * z ^ 2 ≠ p.obstructionScale * p.truant := by
  have hcheck : 0 < p.modulus ∧
      ∀ a ∈ squareResidues p.modulus, ∀ b ∈ squareResidues p.modulus,
        ∀ c ∈ squareResidues p.modulus,
          (p.obstructionCoefficients.1 * a +
            p.obstructionCoefficients.2.1 * b +
            p.obstructionCoefficients.2.2 * c) % p.modulus ≠
            p.obstructionScale * p.truant % p.modulus := by
    simpa only [checkObstruction, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] using h
  have hres := hcheck.2 (x ^ 2 % p.modulus) (square_mod_mem _ _ hcheck.1)
    (y ^ 2 % p.modulus) (square_mod_mem _ _ hcheck.1)
    (z ^ 2 % p.modulus) (square_mod_mem _ _ hcheck.1)
  intro heq
  apply hres
  have heqmod := congrArg (fun n : ℕ => n % p.modulus) heq
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using heqmod

/-- The same holds at integers `x`, `y`, `z`. -/
theorem diagonal_obstruction_int (p : TableOneRow)
    (h : p.checkObstruction = true) (x y z : ℤ) :
    (p.obstructionCoefficients.1 : ℤ) * x ^ 2 +
      (p.obstructionCoefficients.2.1 : ℤ) * y ^ 2 +
      (p.obstructionCoefficients.2.2 : ℤ) * z ^ 2 ≠
        ((p.obstructionScale * p.truant : ℕ) : ℤ) := by
  intro heq
  apply p.diagonal_obstruction_nat h x.natAbs y.natAbs z.natAbs
  have habs :
      ((p.obstructionCoefficients.1 * x.natAbs ^ 2 +
        p.obstructionCoefficients.2.1 * y.natAbs ^ 2 +
        p.obstructionCoefficients.2.2 * z.natAbs ^ 2 : ℕ) : ℤ) =
      ((p.obstructionScale * p.truant : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Int.natCast_natAbs, sq_abs] using heq
  exact_mod_cast habs

end TableOneRow

theorem tableOneRow_obstruction_checked (i : Fin 10) :
    (tableOneRow i).checkObstruction = true :=
  List.all_eq_true.mp tableOne_congruences_checked (tableOneRow i) (tableOneRow_mem i)

/-- The truant of each row is the Fibonacci number at its index. -/
theorem tableOneRow_fib (i : Fin 10) :
    Nat.fib (tableOneRow i).index = (tableOneRow i).truant := by
  have h := List.all_eq_true.mp tableOne_indices_checked (tableOneRow i) (tableOneRow_mem i)
  simpa using h

theorem tableOneRow_diagonal_obstruction (i : Fin 10) (x y z : ℤ) :
    ((tableOneRow i).obstructionCoefficients.1 : ℤ) * x ^ 2 +
      ((tableOneRow i).obstructionCoefficients.2.1 : ℤ) * y ^ 2 +
      ((tableOneRow i).obstructionCoefficients.2.2 : ℤ) * z ^ 2 ≠
        (((tableOneRow i).obstructionScale * (tableOneRow i).truant : ℕ) : ℤ) :=
  (tableOneRow i).diagonal_obstruction_int (tableOneRow_obstruction_checked i) x y z

/-- The change of variables of the congruence check: `(x, y, z) ↦ (x, 2y + z, z)`
for the row of `f` (`i = 4`), which gives `2f = 2x² + (2y + z)² + 7z²`, and the
identity for the other rows, which are already diagonal. -/
def tableOneObstructionVector (i : Fin 10) (v : IntTriple) : IntTriple :=
  if i = 4 then (v.1, 2 * v.2.1 + v.2.2, v.2.2) else v

theorem tableOneRow_obstruction_identity (i : Fin 10) (v : IntTriple) :
    ((tableOneRow i).obstructionScale : ℤ) * (tableOneRow i).eval v =
      ((tableOneRow i).obstructionCoefficients.1 : ℤ) *
        (tableOneObstructionVector i v).1 ^ 2 +
      ((tableOneRow i).obstructionCoefficients.2.1 : ℤ) *
        (tableOneObstructionVector i v).2.1 ^ 2 +
      ((tableOneRow i).obstructionCoefficients.2.2 : ℤ) *
        (tableOneObstructionVector i v).2.2 ^ 2 := by
  fin_cases i
  all_goals norm_num [tableOneRow, tableOne, TableOneRow.eval,
    tableOneObstructionVector]
  all_goals ring

/-- The congruence check of Table 1: each escalator `P_t` omits its truant `t`. -/
theorem tableOneRow_polynomial_omits (i : Fin 10) :
    ¬ ∃ v : IntTriple,
      (tableOneRow i).eval v = ((tableOneRow i).truant : ℤ) := by
  rintro ⟨v, hv⟩
  apply tableOneRow_diagonal_obstruction i
    (tableOneObstructionVector i v).1
    (tableOneObstructionVector i v).2.1
    (tableOneObstructionVector i v).2.2
  simpa only [hv, Nat.cast_mul] using (tableOneRow_obstruction_identity i v).symm

end FibonacciCriterion
