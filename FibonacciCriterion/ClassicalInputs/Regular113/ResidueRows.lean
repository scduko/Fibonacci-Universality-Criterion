import Mathlib

/-!
# Residue tables for the `⟨1,1,3⟩` Mordell construction

The Mordell construction for `⟨1,1,3⟩` takes a square parameter and a residue
of the auxiliary prime from a table indexed by the input modulo 8 or 16:
`IsUnramified113Row` for `3 ∤ m` and `IsRamified113Row` for `m = 3m₁`. This
file proves that each table covers every input not divisible by 4, that the
progressions `unramified113Residue` and `ramified113Residue` are invertible
modulo `8m` and `8m₁`, and that their members satisfy the separator identity,
which makes the leading coefficient of the Mordell form `≡ 5 (mod 8)`.
Dirichlet's theorem and reciprocity are applied in
`ClassicalInputs.Regular113.Mordell`.
-/

namespace FibonacciCriterion.MordellRegularity

/-- The table for `3 ∤ m`: a row gives the square parameter `A` and an integer
`α` with `a ≡ α (mod 8)` for the auxiliary prime `a` (in the even rows `α` is
the residue of `a` modulo 16), according to `m` modulo 8 (odd `m`) or modulo
16 (`m ≡ 2 (mod 4)`). -/
def IsUnramified113Row (m A α : ℕ) : Prop :=
  (m % 8 = 1 ∧ A = 2 ∧ α = 1) ∨
  (m % 8 = 3 ∧ A = 8 ∧ α = 7) ∨
  (m % 8 = 5 ∧ A = 8 ∧ α = 1) ∨
  (m % 8 = 7 ∧ A = 2 ∧ α = 7) ∨
  (m % 16 = 2 ∧ A = 3 ∧ α = 1) ∨
  (m % 16 = 6 ∧ A = 1 ∧ α = 13) ∨
  (m % 16 = 10 ∧ A = 1 ∧ α = 1) ∨
  (m % 16 = 14 ∧ A = 3 ∧ α = 13)

/-- Every `m` with `4 ∤ m` has a row in the unramified table. -/
theorem exists_unramified113_row (m : ℕ) (h4 : ¬ 4 ∣ m) :
    ∃ A α : ℕ, IsUnramified113Row m A α := by
  have hr0 : 0 ≤ m % 16 := Nat.zero_le _
  have hr16 : m % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hmod4 : m % 4 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using h4
  have hreduce4 : (m % 16) % 4 = m % 4 :=
    Nat.mod_mod_of_dvd m (by norm_num)
  have hreduce8 : (m % 16) % 8 = m % 8 :=
    Nat.mod_mod_of_dvd m (by norm_num)
  interval_cases h : m % 16
  · simp at hreduce4
    omega
  · have hm8 : m % 8 = 1 := by
      simp at hreduce8
      omega
    exact ⟨2, 1, by simp [IsUnramified113Row, hm8]⟩
  · exact ⟨3, 1, by simp [IsUnramified113Row, h]⟩
  · have hm8 : m % 8 = 3 := by
      simp at hreduce8
      omega
    exact ⟨8, 7, by simp [IsUnramified113Row, hm8]⟩
  · simp at hreduce4
    omega
  · have hm8 : m % 8 = 5 := by
      simp at hreduce8
      omega
    exact ⟨8, 1, by simp [IsUnramified113Row, hm8]⟩
  · exact ⟨1, 13, by simp [IsUnramified113Row, h]⟩
  · have hm8 : m % 8 = 7 := by
      simp at hreduce8
      omega
    exact ⟨2, 7, by simp [IsUnramified113Row, hm8]⟩
  · simp at hreduce4
    omega
  · have hm8 : m % 8 = 1 := by
      simp at hreduce8
      omega
    exact ⟨2, 1, by simp [IsUnramified113Row, hm8]⟩
  · exact ⟨1, 1, by simp [IsUnramified113Row, h]⟩
  · have hm8 : m % 8 = 3 := by
      simp at hreduce8
      omega
    exact ⟨8, 7, by simp [IsUnramified113Row, hm8]⟩
  · simp at hreduce4
    omega
  · have hm8 : m % 8 = 5 := by
      simp at hreduce8
      omega
    exact ⟨8, 1, by simp [IsUnramified113Row, hm8]⟩
  · exact ⟨3, 13, by simp [IsUnramified113Row, h]⟩
  · have hm8 : m % 8 = 7 := by
      simp at hreduce8
      omega
    exact ⟨2, 7, by simp [IsUnramified113Row, hm8]⟩

/-- For `3 ∤ m`, the square parameter `A` of a row is prime to `m`: in the
odd rows `A` is a power of 2, and in the even rows `A` is 1 or 3. Hence
`-A²` is invertible modulo `m`. -/
theorem unramified113_row_coprime {m A α : ℕ}
    (h3 : ¬ 3 ∣ m) (h : IsUnramified113Row m A α) :
    m.Coprime A := by
  have odd_coprime_two (hm : m % 2 = 1) : m.Coprime 2 := by
    rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    intro hd
    have hz : m % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  have coprime_three : m.Coprime 3 := by
    rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
    exact h3
  rcases h with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨hm, rfl, rfl⟩
  · exact (odd_coprime_two (by omega)).pow_right 1
  · simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using
      (odd_coprime_two (by omega)).pow_right 3
  · simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using
      (odd_coprime_two (by omega)).pow_right 3
  · exact (odd_coprime_two (by omega)).pow_right 1
  · exact coprime_three
  · simp
  · simp
  · exact coprime_three

/-- The residue `m(8A² + 5) - A²` of the unramified progression modulo `8m`.
A prime `p` in this class satisfies `A² + p ≡ 5m (mod 8m)` and
`p ≡ α (mod 8)`. -/
def unramified113Residue (m A : ℕ) : ℕ :=
  m * (8 * A ^ 2 + 5) - A ^ 2

/-- `A² + unramified113Residue m A = m(8A² + 5)`. -/
theorem unramified113_residue_identity {m A α : ℕ} (hm : 0 < m)
    (h : IsUnramified113Row m A α) :
    A ^ 2 + unramified113Residue m A = m * (8 * A ^ 2 + 5) := by
  rcases h with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨hr, rfl, rfl⟩ <;>
    simp [unramified113Residue] at hr ⊢ <;> omega

/-- `unramified113Residue m A ≡ α (mod 8)`. -/
theorem unramified113_residue_mod_eight {m A α : ℕ} (hm : 0 < m)
    (h : IsUnramified113Row m A α) :
    unramified113Residue m A % 8 = α % 8 := by
  rcases h with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨hr, rfl, rfl⟩ <;>
    simp [unramified113Residue] at hr ⊢ <;> omega

/-- For `3 ∤ m`, `unramified113Residue m A` is prime to `8m`, so Dirichlet's
theorem applies to its class. The condition modulo 3 is added in
`ClassicalInputs.Regular113.Mordell`. -/
theorem unramified113_residue_coprime {m A α : ℕ} (hm : 0 < m)
    (h3 : ¬ 3 ∣ m) (h : IsUnramified113Row m A α) :
    (unramified113Residue m A).Coprime (8 * m) := by
  let r := unramified113Residue m A
  have hid : A ^ 2 + r = m * (8 * A ^ 2 + 5) :=
    unramified113_residue_identity hm h
  have hAm : m.Coprime (A ^ 2) := (unramified113_row_coprime h3 h).pow_right 2
  have hrm : r.Coprime m := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hsum : r.gcd m ∣ A ^ 2 + r := by
      rw [hid]
      exact (Nat.gcd_dvd_right r m).trans (dvd_mul_right m _)
    have hA : r.gcd m ∣ A ^ 2 := by
      rw [Nat.add_comm] at hsum
      exact (Nat.dvd_add_iff_right (Nat.gcd_dvd_left r m)).mpr hsum
    exact Nat.eq_one_of_dvd_coprimes hAm
      (Nat.gcd_dvd_right r m) hA
  have hr2 : ¬ 2 ∣ r := by
    intro hd
    have hz : r % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    have h8 := unramified113_residue_mod_eight hm h
    rcases h with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hrow, rfl, rfl⟩ <;>
      norm_num at h8 hz <;> omega
  have hr8 : r.Coprime 8 := by
    have hr2c : r.Coprime 2 := by
      simpa [Nat.coprime_comm] using
        (Nat.prime_two.coprime_iff_not_dvd.mpr hr2)
    simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hr2c.pow_right 3
  exact hr8.mul_right hrm

/-- If `p = unramified113Residue m A + 8mk`, then
`A² + p = m(8(A² + k) + 5)`. -/
theorem unramified113_prime_separator {m A α p k : ℕ} (hm : 0 < m)
    (h : IsUnramified113Row m A α)
    (hp : p = unramified113Residue m A + (8 * m) * k) :
    A ^ 2 + p = m * (8 * (A ^ 2 + k) + 5) := by
  rw [hp, ← Nat.add_assoc, unramified113_residue_identity hm h]
  ring

/-- The table for the ramified case `m = 3m₁`: a row gives `A₀`, with
`A = 3A₀`, and the residue `α` modulo 8 of the auxiliary prime `a₁`,
according to `m₁` modulo 8. -/
def IsRamified113Row (m₁ A₀ α : ℕ) : Prop :=
  (m₁ % 8 = 1 ∧ A₀ = 2 ∧ α = 1) ∨
  (m₁ % 8 = 2 ∧ A₀ = 1 ∧ α = 7) ∨
  (m₁ % 8 = 3 ∧ A₀ = 2 ∧ α = 3) ∨
  (m₁ % 8 = 5 ∧ A₀ = 2 ∧ α = 5) ∨
  (m₁ % 8 = 6 ∧ A₀ = 1 ∧ α = 3) ∨
  (m₁ % 8 = 7 ∧ A₀ = 2 ∧ α = 7)

/-- Every `m₁` with `4 ∤ m₁` has a row in the ramified table. -/
theorem exists_ramified113_row (m₁ : ℕ) (h4 : ¬ 4 ∣ m₁) :
    ∃ A₀ α : ℕ, IsRamified113Row m₁ A₀ α := by
  have hr0 : 0 ≤ m₁ % 8 := Nat.zero_le _
  have hr8 : m₁ % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hmod4 : m₁ % 4 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using h4
  have hreduce : (m₁ % 8) % 4 = m₁ % 4 :=
    Nat.mod_mod_of_dvd m₁ (by norm_num)
  interval_cases h : m₁ % 8 <;>
    simp [IsRamified113Row, h] <;> omega

/-- The residue `m₁(8A₀² + 5) - 3A₀²` of the ramified progression modulo
`8m₁`. -/
def ramified113Residue (m₁ A₀ : ℕ) : ℕ :=
  m₁ * (8 * A₀ ^ 2 + 5) - 3 * A₀ ^ 2

/-- `3A₀² + ramified113Residue m₁ A₀ = m₁(8A₀² + 5)`. Multiplying by 3
gives the separator identity for `m = 3m₁` and `A = 3A₀`. -/
theorem ramified113_residue_identity {m₁ A₀ α : ℕ} (hm₁ : 0 < m₁)
    (h : IsRamified113Row m₁ A₀ α) :
    3 * A₀ ^ 2 + ramified113Residue m₁ A₀ =
      m₁ * (8 * A₀ ^ 2 + 5) := by
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨hr, rfl, rfl⟩ <;>
    simp [ramified113Residue] at hr ⊢ <;> omega

/-- `ramified113Residue m₁ A₀ ≡ α (mod 8)`. -/
theorem ramified113_residue_mod_eight {m₁ A₀ α : ℕ} (hm₁ : 0 < m₁)
    (h : IsRamified113Row m₁ A₀ α) :
    ramified113Residue m₁ A₀ % 8 = α % 8 := by
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨hr, rfl, rfl⟩ <;>
    simp [ramified113Residue] at hr ⊢ <;> omega

/-- For `3 ∤ m₁`, `ramified113Residue m₁ A₀` is prime to `8m₁`. The proof
uses that `α` is odd and that 3 and `A₀` are prime to `m₁`. -/
theorem ramified113_residue_coprime {m₁ A₀ α : ℕ} (hm₁ : 0 < m₁)
    (h3 : ¬ 3 ∣ m₁) (h : IsRamified113Row m₁ A₀ α) :
    (ramified113Residue m₁ A₀).Coprime (8 * m₁) := by
  let r := ramified113Residue m₁ A₀
  have hid : 3 * A₀ ^ 2 + r = m₁ * (8 * A₀ ^ 2 + 5) :=
    ramified113_residue_identity hm₁ h
  have hm3 : m₁.Coprime 3 := by
    rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
    exact h3
  have htwo (hr : m₁ % 2 = 1) : m₁.Coprime 2 := by
    rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    intro hd
    have hz : m₁ % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  have hmA : m₁.Coprime A₀ := by
    rcases h with h | h | h | h | h | h <;>
      rcases h with ⟨hr, rfl, rfl⟩
    all_goals first
      | exact (by simp : m₁.Coprime 1)
      | exact htwo (by omega)
  have hm3A : m₁.Coprime (3 * A₀ ^ 2) := hm3.mul_right (hmA.pow_right 2)
  have hrm : r.Coprime m₁ := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hsum : r.gcd m₁ ∣ 3 * A₀ ^ 2 + r := by
      rw [hid]
      exact (Nat.gcd_dvd_right r m₁).trans (dvd_mul_right m₁ _)
    have hA : r.gcd m₁ ∣ 3 * A₀ ^ 2 := by
      rw [Nat.add_comm] at hsum
      exact (Nat.dvd_add_iff_right (Nat.gcd_dvd_left r m₁)).mpr hsum
    exact Nat.eq_one_of_dvd_coprimes hm3A
      (Nat.gcd_dvd_right r m₁) hA
  have hr2 : ¬ 2 ∣ r := by
    intro hd
    have hz : r % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    have h8 := ramified113_residue_mod_eight hm₁ h
    rcases h with h | h | h | h | h | h <;>
      rcases h with ⟨hr, rfl, rfl⟩ <;> norm_num at h8 hz <;> omega
  have hr8 : r.Coprime 8 := by
    have hr2c : r.Coprime 2 := by
      simpa [Nat.coprime_comm] using
        (Nat.prime_two.coprime_iff_not_dvd.mpr hr2)
    simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hr2c.pow_right 3
  exact hr8.mul_right hrm

/-- If `p = ramified113Residue m₁ A₀ + 8m₁k`, then
`3A₀² + p = m₁(8(A₀² + k) + 5)`. -/
theorem ramified113_prime_separator {m₁ A₀ α p k : ℕ} (hm₁ : 0 < m₁)
    (h : IsRamified113Row m₁ A₀ α)
    (hp : p = ramified113Residue m₁ A₀ + (8 * m₁) * k) :
    3 * A₀ ^ 2 + p = m₁ * (8 * (A₀ ^ 2 + k) + 5) := by
  rw [hp, ← Nat.add_assoc, ramified113_residue_identity hm₁ h]
  ring

end FibonacciCriterion.MordellRegularity
