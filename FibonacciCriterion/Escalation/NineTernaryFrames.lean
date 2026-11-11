import FibonacciCriterion.Escalation.NineTernaryEscalators
import FibonacciCriterion.Escalation.BinaryOneOne
import FibonacciCriterion.Escalation.BinaryOneTwo

/-!
# Escalation to the nine ternary escalators (Proposition 3.1)

Every form that represents 1, 2, 3, and 5 contains a frame of one of the nine
ternary escalators: three vectors with its Gram matrix
(`exists_nine_ternary_frame`). The conclusion lists the six Gram entries;
`Form.IsFrame` in `Escalation.QuaternaryEscalation` packages them, with each
pairing transposed, and `Criterion.Sufficiency` converts by symmetry. The
proof follows the manuscript's proof of Proposition 3.1, by integral
projection onto the vectors of norm 1 and reduction along the vector of
norm 2. The three vectors need not extend to a basis. The manuscript also
shows that each of the nine forms occurs and that they are pairwise
inequivalent; the criterion does not need this, and it is not formalized.
-/

namespace FibonacciCriterion
namespace Form

variable {ι : Type*} [Fintype ι]

/-- Proposition 3.1: every form that represents 1, 2, 3, and 5 contains vectors
`v`, `u`, `r` with the Gram matrix `escalatorGram b d e` of one of the nine
ternary escalators. -/
theorem exists_nine_ternary_frame (P : Form ι)
    (h1 : P.Represents 1) (h2 : P.Represents 2)
    (h3 : P.Represents 3) (h5 : P.Represents 5) :
    ∃ b d e : ℤ, ∃ v u r : ι → ℤ,
      NineTernaryEscalator b d e ∧
      P.eval v = 1 ∧ P.eval u = b ∧ P.eval r = d ∧
      P.pairing u v = 0 ∧ P.pairing r v = 0 ∧ P.pairing r u = e := by
  obtain ⟨v, u, hv, huv, hu | hu⟩ := P.exists_first_binary_pair h1 h2
  · obtain ⟨r, hrv, hru, hd⟩ :=
      P.exists_ternary_of_unit_pair v u hv hu huv h3
    exact ⟨1, P.eval r, 0, v, u, r,
      Or.inl ⟨rfl, rfl, hd⟩, hv, hu, rfl, huv, hrv, hru⟩
  · obtain ⟨r, hrv, he, hd, hd', hsharp⟩ :=
      P.exists_oneTwo_reduced_vector v u hv hu huv h5
    rcases he with he | he
    · by_cases hd1 : P.eval r = 1
      · refine ⟨1, 2, 0, v, r, u, ?_, hv, hd1, hu, hrv, huv, ?_⟩
        · norm_num [NineTernaryEscalator]
        · exact (P.pairing_comm u r).trans he
      · have hds : P.eval r = 2 ∨ P.eval r = 3 ∨
            P.eval r = 4 ∨ P.eval r = 5 := by omega
        exact ⟨2, P.eval r, 0, v, u, r,
          Or.inr (Or.inl ⟨rfl, rfl, hds⟩), hv, hu, rfl, huv, hrv, he⟩
    · rcases hsharp he with hd1 | hd4 | hd5
      · have hs := P.mixed_unit_split u r hu hd1 he
        have huv' : P.pairing (u - r) v = 0 := by
          rw [pairing_sub_left, huv, hrv]
          norm_num
        refine ⟨1, 1, 0, v, r, u - r, ?_, hv, hd1, hs.1, hrv, huv', hs.2⟩
        norm_num [NineTernaryEscalator]
      · refine ⟨2, 4, 1, v, u, r, ?_, hv, hu, hd4, huv, hrv, he⟩
        norm_num [NineTernaryEscalator]
      · refine ⟨2, 5, 1, v, u, r, ?_, hv, hu, hd5, huv, hrv, he⟩
        norm_num [NineTernaryEscalator]

end Form
end FibonacciCriterion
