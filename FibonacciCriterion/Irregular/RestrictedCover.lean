import FibonacciCriterion.Fibonacci.Period

/-!
# The congruence cover (Lemma 6.6)

`restricted_cover` is Lemma 6.6: for `q ∈ Q₇ \ {7}` and an index `n` whose
residue pair `(q mod 12, Fₙ mod 12)` is one of the four pairs in (7), some
prime `p` of the ten-prime set `P₇` satisfies `p ∤ q` and
`Fₙ mod p ∈ q (𝔽_p^×)²`. It is stated for the twenty values of `q` that are 0,
3, or 9 modulo 12 (`restrictedCoefficients`); the others never meet (7). In
the names of this file, `restricted` refers to this restriction to the twenty
values of `q` and to the index classes that meet (7).

The proof follows the manuscript's eight groups of the twenty relevant
values of `q` and their primes. For each group, the residues of `Fₙ` modulo 12
and modulo the group's primes depend only on `n` modulo a common return time
`M` (72, 120, 168, or 216). `CoverGroup.check` walks the Fibonacci state
modulo `12 ∏ p` through one return time and checks the case analysis on each
residue class of `n` modulo `M`. The manuscript argues by quadratic
characters; the check instead searches for a nonzero `k < p` with
`q k² ≡ Fₙ (mod p)`, which is equivalent, and does so only on the classes
where `(q, Fₙ)` meets a pair in (7).
-/

namespace FibonacciCriterion.RestrictedCover

/-- The set `P₇` of §6.3: the ten primes of Lemmas 6.5 and 6.6. -/
def coverPrimes : List ℕ := [5, 11, 13, 17, 19, 31, 53, 83, 107, 109]

/-- The pair `(q mod 12, a)` is one of the four residue pairs in (7). These are
the pairs of `Irregular.BadPair` (`badPair_iff`). -/
def BadResidue (q a : ℕ) : Prop :=
  (q % 12 = 0 ∧ (a = 7 ∨ a = 10)) ∨ (q % 12 = 3 ∧ a = 10) ∨ (q % 12 = 9 ∧ a = 7)

instance (q a : ℕ) : Decidable (BadResidue q a) := by
  unfold BadResidue
  infer_instance

/-- `LocalRoot q p a k`: `p ∤ q`, `p ∤ k`, and `a` is the residue of `q k²`
modulo `p`. -/
def LocalRoot (q p a k : ℕ) : Prop :=
  q % p ≠ 0 ∧ k % p ≠ 0 ∧ a = q * k ^ 2 % p

instance (q p a k : ℕ) : Decidable (LocalRoot q p a k) := by
  unfold LocalRoot
  infer_instance

/-- The conclusion of Lemma 6.6 for `q` at the index `n`: the pair
`(q mod 12, Fₙ mod 12)` is not in (7), or some `p ∈ P₇` and `k` satisfy
`LocalRoot q p (Fₙ mod p) k`. -/
def Covered (q n : ℕ) : Prop :=
  ¬ BadResidue q (Nat.fib n % 12) ∨
    ∃ p ∈ coverPrimes, ∃ k : ℕ, LocalRoot q p (Nat.fib n % p) k

/-- One group of values of `q` in the proof of Lemma 6.6, with its primes and
a common return time `M` of the Fibonacci state modulo 12 and modulo those
primes. -/
structure CoverGroup where
  /-- The values of `q` in the group. -/
  coefficients : List ℕ
  /-- The primes of `P₇` used for the group. -/
  primes : List ℕ
  /-- The return time `M` of the group. -/
  period : ℕ

/-- The search over `k < p` for `LocalRoot q p a k`; for `a < p` it succeeds
if and only if `p ∤ q` and `a ∈ q (𝔽_p^×)²`. -/
def hasRoot (q p a : ℕ) : Bool :=
  (List.range p).any fun k => decide (LocalRoot q p a k)

/-- A successful search gives a local root. -/
theorem exists_localRoot_of_hasRoot {q p a : ℕ} (h : hasRoot q p a = true) :
    ∃ k, LocalRoot q p a k := by
  simp only [hasRoot, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨k, -, hk⟩ := h
  exact ⟨k, hk⟩

/-- The check at one index class, given `Fᵣ mod L`: each value of `q` in the
group either avoids (7) or has a local root at one of the group's primes. -/
def CoverGroup.classCheck (g : CoverGroup) (a : ℕ) : Bool :=
  g.coefficients.all fun q =>
    !decide (BadResidue q (a % 12)) || g.primes.any fun p => hasRoot q p (a % p)

/-- The walk of the Fibonacci state modulo `L` through `s` steps: it checks
each class on the way and then checks that the state has returned to
`(0, 1)`. -/
def CoverGroup.walk (g : CoverGroup) (L : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, a, b => a == 0 && b == 1 % L
  | s + 1, a, b => g.classCheck a && g.walk L s b ((a + b) % L)

/-- If a walk of `s` steps started at the state at `r` succeeds, then the
classes `r, …, r + s - 1` pass `classCheck` and the state at `r + s` is
`(0, 1)`. -/
theorem CoverGroup.walk_sound (g : CoverGroup) (L : ℕ) (s : ℕ) :
    ∀ r, g.walk L s (Nat.fib r % L) (Nat.fib (r + 1) % L) = true →
      (∀ j < s, g.classCheck (Nat.fib (r + j) % L) = true) ∧
        Nat.fib (r + s) % L = 0 ∧ Nat.fib (r + s + 1) % L = 1 % L := by
  induction s with
  | zero =>
    intro r h
    simp only [CoverGroup.walk, Bool.and_eq_true, beq_iff_eq] at h
    simpa using h
  | succ s ih =>
    intro r h
    simp only [CoverGroup.walk, Bool.and_eq_true] at h
    obtain ⟨h0, h1⟩ := h
    have hstep : (Nat.fib r % L + Nat.fib (r + 1) % L) % L = Nat.fib (r + 1 + 1) % L := by
      rw [Nat.fib_add_two]
      exact (Nat.add_mod _ _ _).symm
    rw [hstep] at h1
    obtain ⟨hj, hend⟩ := ih (r + 1) h1
    refine ⟨?_, ?_⟩
    · intro j hj'
      rcases j with _ | j
      · simpa using h0
      · have := hj j (by omega)
        rwa [show r + 1 + j = r + (j + 1) by omega] at this
    · rwa [show r + 1 + s = r + (s + 1) by omega] at hend

/-- The common modulus `12 ∏ p` of a group. -/
def CoverGroup.modulus (g : CoverGroup) : ℕ := 12 * g.primes.prod

/-- The checks for one group: `M > 0`, every prime is in `P₇`, every residue
class of the index modulo `M` passes `classCheck`, and the Fibonacci state
modulo `12 ∏ p` returns to `(0, 1)` at `M`. -/
def CoverGroup.check (g : CoverGroup) : Bool :=
  decide (0 < g.period ∧ ∀ p ∈ g.primes, p ∈ coverPrimes) &&
    g.walk g.modulus g.period 0 (1 % g.modulus)

/-- A return time modulo `m` is a return time modulo every divisor of `m`. -/
theorem fibStateReturns_of_dvd {m d T : ℕ} (h : FibStateReturns m T) (hd : d ∣ m) :
    FibStateReturns d T := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_mod_of_dvd _ hd, h0, Nat.zero_mod]
  · rw [← Nat.mod_mod_of_dvd _ hd, h1, Nat.mod_mod_of_dvd _ hd]

/-- A checked group covers every index for each of its values of `q`. -/
theorem CoverGroup.covered (g : CoverGroup) (hg : g.check = true)
    {q : ℕ} (hq : q ∈ g.coefficients) (n : ℕ) : Covered q n := by
  simp only [CoverGroup.check, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hM, hprimes⟩, hwalk⟩ := hg
  have hwalk' := g.walk_sound g.modulus g.period 0 (by simpa using hwalk)
  obtain ⟨hclasses, hend0, hend1⟩ := hwalk'
  simp only [Nat.zero_add] at hclasses hend0 hend1
  have hL : FibStateReturns g.modulus g.period := ⟨hend0, hend1⟩
  have h12L : 12 ∣ g.modulus := Dvd.intro _ rfl
  have h12 : FibStateReturns 12 g.period := fibStateReturns_of_dvd hL h12L
  have hclass := hclasses (n % g.period) (Nat.mod_lt n hM)
  simp only [CoverGroup.classCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true] at hclass
  rcases hclass q hq with hgood | ⟨p, hp, hroot⟩
  · left
    have hmod : Nat.fib (n % g.period) % g.modulus % 12 = Nat.fib n % 12 := by
      rw [Nat.mod_mod_of_dvd _ h12L, ← fib_mod_reduce_index 12 g.period h12 n]
    rwa [hmod] at hgood
  · right
    have hpL : p ∣ g.modulus :=
      Dvd.dvd.mul_left (List.dvd_prod hp) 12
    have hmod : Nat.fib (n % g.period) % g.modulus % p = Nat.fib n % p := by
      rw [Nat.mod_mod_of_dvd _ hpL,
        ← fib_mod_reduce_index p g.period (fibStateReturns_of_dvd hL hpL) n]
    rw [hmod] at hroot
    obtain ⟨k, hk⟩ := exists_localRoot_of_hasRoot hroot
    exact ⟨p, hprimes p hp, k, hk⟩

/-- The values 3 and 903 of `q`, with primes 5 and 11 and return time 120. -/
def group3 : CoverGroup := ⟨[3, 903], [5, 11], 120⟩
/-- The values 12, 168, 672 of `q`, with primes 5, 11, 31 and return time 120. -/
def group12 : CoverGroup := ⟨[12, 168, 672], [5, 11, 31], 120⟩
/-- The values 15, 231, 483, 819 of `q`, with prime 19 and return time 72. -/
def group15 : CoverGroup := ⟨[15, 231, 483, 819], [19], 72⟩
/-- The values 21, 84, 189, 336, 525, 756 of `q`, with primes 17 and 19 and
return time 72. -/
def group21 : CoverGroup := ⟨[21, 84, 189, 336, 525, 756], [17, 19], 72⟩
/-- The values 9 and 777 of `q`, with primes 13 and 83 and return time 168. -/
def group9 : CoverGroup := ⟨[9, 777], [13, 83], 168⟩
/-- The value 315 of `q`, with prime 107 and return time 72. -/
def group315 : CoverGroup := ⟨[315], [107], 72⟩
/-- The value 609 of `q`, with primes 17, 53, 109 and return time 216. -/
def group609 : CoverGroup := ⟨[609], [17, 53, 109], 216⟩
/-- The value 924 of `q`, with primes 19 and 53 and return time 216. -/
def group924 : CoverGroup := ⟨[924], [19, 53], 216⟩

/-- The eight groups of values of `q` in Lemma 6.6. -/
def coverGroups : List CoverGroup :=
  [group3, group12, group15, group21, group9, group315, group609, group924]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Each of the eight groups passes `CoverGroup.check`. -/
theorem coverGroups_checked : coverGroups.all CoverGroup.check = true := by
  decide +kernel

/-- The twenty elements of `Q₇ \ {7}` congruent to 0, 3, or 9 modulo 12
(`restrictedCoefficients_complete` in `Irregular.LargeIndices` proves that
every such element is listed). -/
def restrictedCoefficients : List ℕ :=
  [3, 9, 12, 15, 21, 84, 168, 189, 231, 315, 336, 483, 525, 609, 672, 756, 777,
    819, 903, 924]

/-- Each of the twenty values of `q` lies in one of the eight groups. -/
theorem restrictedCoefficients_grouped :
    ∀ q ∈ restrictedCoefficients, ∃ g ∈ coverGroups, q ∈ g.coefficients := by
  decide

/-- Lemma 6.6: for each of the twenty values of `q` that can meet a pair in
(7) and every index `n`, either `(q mod 12, Fₙ mod 12)` is not in (7), or some
`p ∈ P₇` satisfies `p ∤ q` and `Fₙ mod p ∈ q (𝔽_p^×)²`. -/
theorem restricted_cover (q : ℕ) (hq : q ∈ restrictedCoefficients) (n : ℕ) :
    Covered q n := by
  obtain ⟨g, hg, hqg⟩ := restrictedCoefficients_grouped q hq
  exact g.covered (List.all_eq_true.mp coverGroups_checked g hg) hqg n

end FibonacciCriterion.RestrictedCover
