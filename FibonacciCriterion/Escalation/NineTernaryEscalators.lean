import FibonacciCriterion.Escalation.Pairing
import FibonacciCriterion.Forms.TernaryGram

/-!
# The nine ternary escalators

The Gram matrices of the nine ternary escalators of Proposition 3.1
(`NineTernaryEscalator`, `escalatorGram`), and the splitting
(`mixed_unit_split`) that reduces the case of pairing 1 and third norm 1 in
its proof to `⟨1,1,1⟩`. `Escalation.NineTernaryFrames` proves that every form that
represents 1, 2, 3, and 5 contains a frame of one of them.
-/

namespace FibonacciCriterion

/-- The parameters `(b, d, e)` of the nine ternary escalators
`x² + b y² + 2e yz + d z²`: `⟨1,1,1⟩`, `⟨1,1,2⟩`, `⟨1,1,3⟩`, `⟨1,2,2⟩`,
`⟨1,2,3⟩`, `⟨1,2,4⟩`, `⟨1,2,5⟩`, `f` (`b = 2`, `e = 1`, `d = 4`), and `g`
(`b = 2`, `e = 1`, `d = 5`). In the manuscript's proof of Proposition 3.1 the
pairing is `b` and the third diagonal entry is `m`; here they are `e` and
`d`. -/
def NineTernaryEscalator (b d e : ℤ) : Prop :=
  (b = 1 ∧ e = 0 ∧ (d = 1 ∨ d = 2 ∨ d = 3)) ∨
  (b = 2 ∧ e = 0 ∧ (d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5)) ∨
  (b = 2 ∧ e = 1 ∧ (d = 4 ∨ d = 5))

/-- The Gram matrix `[[1,0,0],[0,b,e],[0,e,d]]` of `x² + b y² + 2e yz + d z²`. -/
abbrev escalatorGram (b d e : ℤ) : TernaryGram := ⟨1, b, d, 0, 0, e⟩

namespace Form

variable {ι : Type*} [Fintype ι]

/-- If `P(u) = 2`, `P(r) = 1`, and `β(r, u) = 1`, then `u - r` has norm 1 and is
orthogonal to `r`: the identity `x² + 2y² + 2yz + z² = x² + y² + (y + z)²`. -/
theorem mixed_unit_split (P : Form ι) (u r : ι → ℤ)
    (hu : P.eval u = 2) (hr : P.eval r = 1)
    (hru : P.pairing r u = 1) :
    P.eval (u - r) = 1 ∧ P.pairing (u - r) r = 0 := by
  have hur : P.pairing u r = 1 := (P.pairing_comm u r).trans hru
  have horth : P.pairing (u - r) r = 0 := by
    rw [pairing_sub_left, pairing_self, hur, hr]
    norm_num
  have hrev : P.pairing r (u - r) = 0 := (P.pairing_comm r _).trans horth
  have he := P.eval_add_pairing (u - r) r
  rw [sub_add_cancel, hu, horth, hrev, hr] at he
  exact ⟨by omega, horth⟩

end Form
end FibonacciCriterion
