import Mathlib

/-!
# The ten escalators of Table 1

`tableOne` lists the rows of Table 1. Each row records an element
`t = Fₙ` of `criterion` and its index `n`, the escalator `P_t` with truant `t`
as the polynomial `a x² + b y² + 2e yz + c z²` (`e` is the field `yz`; below
rank 3 the unused coordinates have coefficient 0), and the data of the
congruence check of Table 1: a diagonal form `α x² + β y² + γ z²`, equal to
`scale · P_t` after an integral change of variables, whose values modulo
`m_t` omit `scale · t`.

The manuscript states that the values of `P_t` modulo `m_t` omit `t`. For the
row of `f`, the check here uses `2f = 2x² + (2y + z)² + 7z²` modulo 49, which
is equivalent because 2 is a unit modulo 49. The check runs over the squares
modulo `m_t`. `Criterion.TableOneCongruences` proves it sound for all integer coordinates,
`Criterion.TableOneForms` builds each `P_t` as a positive-definite form of rank 0 to 3,
and `Criterion.Indispensability` combines these with the criteria of Proposition 3.2
and the four-square extension.
-/

namespace FibonacciCriterion

/-- An integer vector `(x, y, z)`, at which the polynomial of a row is
evaluated. -/
abbrev IntTriple := ℤ × ℤ × ℤ

/-- A row of Table 1: a truant `t = Fₙ`, the coefficients of the escalator
`P_t = a x² + b y² + 2e yz + c z²`, and the data of its congruence check. -/
structure TableOneRow where
  /-- The truant `t` of the row. -/
  truant : ℕ
  /-- The index `n` with `t = Fₙ`. -/
  index : ℕ
  /-- The coefficient of `x²` in `P_t`. -/
  a : ℤ
  /-- The coefficient of `y²` in `P_t`. -/
  b : ℤ
  /-- The coefficient of `z²` in `P_t`. -/
  c : ℤ
  /-- The Gram-matrix entry `e`; the coefficient of `yz` in `P_t` is `2e`. -/
  yz : ℤ
  /-- The modulus `m_t` of the congruence check. -/
  modulus : ℕ
  /-- The scale of the congruence check: the diagonal form equals
  `scale · P_t` after an integral change of variables. -/
  obstructionScale : ℕ
  /-- The coefficients `(α, β, γ)` of the diagonal form `α x² + β y² + γ z²`
  of the congruence check. -/
  obstructionCoefficients : ℕ × ℕ × ℕ

/-- The value at `v = (x, y, z)` of the polynomial `a x² + b y² + 2e yz + c z²`
of the row. -/
def TableOneRow.eval (p : TableOneRow) (v : IntTriple) : ℤ :=
  p.a * v.1 ^ 2 + p.b * v.2.1 ^ 2 + 2 * p.yz * v.2.1 * v.2.2 +
    p.c * v.2.2 ^ 2

/-- The residues of the squares modulo `m`, listed without repetition. -/
def squareResidues (m : ℕ) : List ℕ :=
  ((List.range m).map (fun r => r * r % m)).eraseDups

/-- The congruence check of the row: `m_t > 0`, and `α x + β y + γ z` is not
congruent to `scale · t` modulo `m_t` for any residues `x`, `y`, `z` of
squares modulo `m_t`. -/
def TableOneRow.checkObstruction (p : TableOneRow) : Bool :=
  decide (0 < p.modulus) &&
  (squareResidues p.modulus).all (fun x =>
    (squareResidues p.modulus).all (fun y =>
      (squareResidues p.modulus).all (fun z =>
        decide ((p.obstructionCoefficients.1 * x +
          p.obstructionCoefficients.2.1 * y +
          p.obstructionCoefficients.2.2 * z) % p.modulus ≠
          p.obstructionScale * p.truant % p.modulus))))

/-- The ten rows of Table 1, in increasing order of the truant. -/
def tableOne : List TableOneRow := [
  { truant := 1, index := 1,
    a := 0, b := 0, c := 0, yz := 0,
    modulus := 2, obstructionScale := 1,
    obstructionCoefficients := (0, 0, 0) },
  { truant := 2, index := 3,
    a := 1, b := 0, c := 0, yz := 0,
    modulus := 4, obstructionScale := 1,
    obstructionCoefficients := (1, 0, 0) },
  { truant := 3, index := 4,
    a := 1, b := 1, c := 0, yz := 0,
    modulus := 4, obstructionScale := 1,
    obstructionCoefficients := (1, 1, 0) },
  { truant := 5, index := 5,
    a := 1, b := 2, c := 0, yz := 0,
    modulus := 8, obstructionScale := 1,
    obstructionCoefficients := (1, 2, 0) },
  { truant := 21, index := 8,
    a := 1, b := 2, c := 4, yz := 1,
    modulus := 49, obstructionScale := 2,
    obstructionCoefficients := (2, 1, 7) },
  { truant := 55, index := 10,
    a := 1, b := 1, c := 1, yz := 0,
    modulus := 8, obstructionScale := 1,
    obstructionCoefficients := (1, 1, 1) },
  { truant := 610, index := 15,
    a := 1, b := 2, c := 5, yz := 0,
    modulus := 25, obstructionScale := 1,
    obstructionCoefficients := (1, 2, 5) },
  { truant := 987, index := 16,
    a := 1, b := 1, c := 3, yz := 0,
    modulus := 9, obstructionScale := 1,
    obstructionCoefficients := (1, 1, 3) },
  { truant := 832040, index := 30,
    a := 1, b := 2, c := 3, yz := 0,
    modulus := 64, obstructionScale := 1,
    obstructionCoefficients := (1, 2, 3) },
  { truant := 267914296, index := 42,
    a := 1, b := 1, c := 2, yz := 0,
    modulus := 64, obstructionScale := 1,
    obstructionCoefficients := (1, 1, 2) }
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The truant of each row is the Fibonacci number at its listed index. -/
theorem tableOne_indices_checked :
    tableOne.all (fun p => decide (Nat.fib p.index = p.truant)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every row passes its congruence check (`checkObstruction`). -/
theorem tableOne_congruences_checked :
    tableOne.all TableOneRow.checkObstruction = true := by
  decide +kernel

theorem tableOne_length : tableOne.length = 10 := rfl

/-- The row of `tableOne` at position `i`, counted from 0. -/
def tableOneRow (i : Fin 10) : TableOneRow :=
  tableOne.get ⟨i.val, by
    simpa only [tableOne_length] using i.isLt⟩

theorem tableOneRow_mem (i : Fin 10) : tableOneRow i ∈ tableOne := by
  exact List.get_mem _ _

end FibonacciCriterion
