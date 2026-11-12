# Fibonacci-Universality Criterion

A Lean 4 formalization of *A Fibonacci Analogue of the Fifteen Theorem*, by
Scott Duke Kominers.

For $C = \lbrace 1, 2, 3, 5, 21, 55, 610, 987, 832040, 267914296 \rbrace$, the
main theorem says that a positive-definite quadratic form with an integral
symmetric Gram matrix represents every Fibonacci number if and only if it
represents every member of $C$. The statement allows arbitrary finite ambient
rank.

## Results

The theorem is proven in Lean with no unproven hypotheses, following the
manuscript. The proof uses no external certificates, data files, or scripts.
Each finite computation is a Lean proposition evaluated by the kernel, together
with a proven lemma that turns it into the statement the proof needs.

The main theorems, in `FibonacciCriterion/Criterion/Theorem.lean`, are:

- `criterionSufficiency`: a form that represents every element
  of $C$ represents every Fibonacci number;
- `fibonacci_criterion`: the characterization above, together
  with the facts that every Fibonacci criterion set contains $C$, that $C$ is
  a minimal criterion set, and that it is the only one;
- `criterionIndispensability`: every set of Fibonacci numbers whose
  representation forces Fibonacci-universality contains $C$;
- `exists_criterion_omission`: for each $t \in C$, some positive-definite
  form represents every Fibonacci number except $t$;
- `fibonacciUniversal_of_represents_fib_le_42` and
  `not_isFibonacciCriterion_fib_le_41` (Corollary 1.2): representing
  $F_1, \dots, F_{42}$ is enough, and representing $F_0, \dots, F_{41}$ is
  not, since $x^2 + y^2 + 2z^2$ represents these numbers but not $F_{42}$;
- `fibonacci_criterion_matrix`: the characterization stated with Mathlib's
  `Matrix.PosDef`, for the quadratic form $x \mapsto x^{\mathsf T} G x$ of an
  integer matrix $G$.

## Where to start

All paths are relative to `FibonacciCriterion/`.

- `Forms.lean` defines positive-definite forms with integral Gram matrices,
  representation, and Fibonacci-universality.
- `Statement.lean` defines $C$ and Fibonacci criterion sets and states the
  criterion. It checks that
  $\lbrace F_n : n \in \lbrace 1, 3, 4, 5, 8, 10, 15, 16, 30, 42 \rbrace
  \rbrace = C$ as sets (`fib_criterionIndices`), where $F_n$ is Mathlib's
  `Nat.fib`, with $F_0 = 0$ and $F_1 = 1$ (`fib_convention`).
- `ClassicalInputs/Definitions.lean` lists the classical results that the
  proof uses, as the fields of one structure.
- `Criterion/Proof.lean` proves the criterion from those results. The
  argument of §7 of the manuscript is in `Criterion/Sufficiency.lean`
  (sufficiency) and `Criterion/Indispensability.lean` (minimality).
- `ClassicalInputs/Theorems.lean` proves the classical results, and
  `Criterion/Theorem.lean` combines the two.
- `Example.lean` applies the theorem to $x^2 + 2y^2 + 5z^2 + 5w^2$, which does
  not represent 15 but represents every Fibonacci number.

The other modules are grouped by section of the manuscript:

| Directory | Content |
| --- | --- |
| `Fibonacci/` | §2: Fibonacci arithmetic |
| `Escalation/` | §3: escalation to the nine ternary forms, Lemma 3.6 |
| `Forms/` | §4: ternary Gram matrices and quaternary extensions |
| `Regular/` | §5: the eight regular ternary forms |
| `Irregular/` | §6: the form $f$ |
| `Criterion/` | §7: sufficiency, minimality (Table 1 and the four-square extension), and the final theorems |
| `ClassicalInputs/` | proofs of the classical results |
| `Arithmetic/` | elementary congruence lemmas |

[docs/READING_GUIDE.md](docs/READING_GUIDE.md) lists every module with the
results of the manuscript that it proves.

## Classical results

The proof uses the following classical results. Each is proven in this
repository or in a pinned dependency.

- The three-square theorem of Gauss and Legendre, from
  [atlas-lean](https://github.com/facebookresearch/atlas-lean).
- The formulas for the 2-, 3-, and 5-adic valuations of $F_n$ (Lemma 2.2).
- The representation criteria for $x^2+y^2+3z^2$, $x^2+2y^2+3z^2$, and
  $x^2+2y^2+5z^2$ (Proposition 3.2), proven by the Mordell-type construction
  of Blackwell, Durham, Thompson, and Treece.
- The sufficiency direction of Proposition 3.3, for $N$ not divisible by 49:
  a positive integer $N$ with $7 \nmid N$, or with $N = 7u$ and
  $u \equiv 1, 2, 4 \pmod 7$, is represented by
  $f = x^2+2y^2+2yz+4z^2$ or by $h = x^2+y^2+7z^2$. The proof uses two
  auxiliary-prime constructions, Minkowski reduction from
  [TauCeti](https://github.com/TauCetiProject/TauCeti), and a kernel-checked
  list of the reduced ternary forms of determinant 7.

Minimality uses only the criteria of Proposition 3.2, which include the
three-square theorem for $x^2+y^2+z^2$.

## Outline of the proof

**Sufficiency (§§3–7).** Let $Q$ be a form that represents every element of
$C$. Because $Q$ represents $1, 2, 3, 5$, it contains a copy of one of nine
ternary forms $T$ (Proposition 3.1):

```math
\langle 1,1,1\rangle,\ \langle 1,1,2\rangle,\ \langle 1,1,3\rangle,\
\langle 1,2,2\rangle,\ \langle 1,2,3\rangle,\ \langle 1,2,4\rangle,\
\langle 1,2,5\rangle,\ f,\ g,
```

where $g = x^2+2y^2+2yz+5z^2$. Each $T$ fails to represent a number
$\tau \in C$, its truant, and also every $k^2\tau$ with $k \neq 0$
(Lemma 3.6). So a vector $u$ of $Q$ with $Q(u) = \tau$ spans, together with
$T$, a lattice $M = T + \mathbb{Z}u$ of rank 4. Lean records $M$ by the
pairings $c$ of $u$ with the basis of $T$ and the norm $m = Q(u)$
(`Forms/QuaternaryExtension.lean`). By Lemmas 4.1 and 4.2, $M$ contains
$T \perp \langle q\rangle$, where $d$ is the denominator of $G_T^{-1}c$ and

```math
q = d^2\bigl(m - c^{\mathsf T} G_T^{-1} c\bigr) \le \tau\,(\det G_T)^2 .
```

Thus $M$ represents $N$ whenever $T$ represents $N - qk^2$ for some integer
$k$. It remains to show that $M$ represents every Fibonacci number:

- for $\langle 1,1,1\rangle$, $\langle 1,1,2\rangle$, $\langle 1,2,2\rangle$,
  $\langle 1,2,3\rangle$, $\langle 1,2,4\rangle$, and $g$, the six ternaries
  with obstructions at 2, by Proposition 5.1
  (`Regular/TwoAdicUniversality.lean`);
- for $\langle 1,1,3\rangle$ and $\langle 1,2,5\rangle$, by Propositions 5.11
  and 5.12 (`Regular/Escalator113.lean`, `Regular/Escalator125.lean`);
- for $f$, by Proposition 6.1 (`Irregular/EscalatorF.lean`).

**The form $f$ (§6).** An extension of $f$ that represents 21 contains
$f \perp \langle q\rangle$ for one of 82 values of $q$ (Lemma 4.4). For $q = 7$, the form
$f \perp \langle 7\rangle$ is universal (Proposition 6.2). For the other
values and $n \ge 48$, subtracting $qk^2$ for a small $k$ (Lemma 6.4) works
unless $(q \bmod 12, F_n \bmod 12)$ is one of four residue pairs. In those cases
Lemma 6.6 finds a prime $p$ in

```math
P_7 = \{5,\ 11,\ 13,\ 17,\ 19,\ 31,\ 53,\ 83,\ 107,\ 109\}
```

with $p \nmid q$ and $F_n \equiv qk^2 \pmod p$ for some $k \not\equiv 0$. The
twenty values of $q$ involved fall into eight groups according to their
quadratic characters at these primes. For each group, Lean follows the
Fibonacci recurrence modulo $12$ and the group's primes through a common period
($72$, $120$, $168$, or $216$; a return time of the Fibonacci state, not
necessarily the least period) and checks the case analysis on every residue
class of $n$. Lemma 6.5 then subtracts $qk^2$, using the integral matrices
$B_p$ of Table 3, which satisfy $B_p^{\mathsf T} G_f B_p = p^2 G_h$;
`Irregular/Transfers.lean` lists them, and `ring` checks each identity. A table
of small primes covers $n = 57, 58$. Proposition 3.5 covers the indices below
$48$, by explicit vectors at a few indices and by Proposition 3.3 and Lemma 3.4
at the others.

**Minimality (§7).** For each $t \in C$, Table 1 gives a form $P_t$ whose
truant is $t$. A congruence, also in Table 1, shows that $P_t$ does not
represent $t$. $P_t$ represents every smaller Fibonacci number: by explicit
vectors when its rank is at most $2$, and by the truant column of Figure 1
(`Escalation/TernaryTruants.lean`) when it is one of the ternary forms. The form

```math
V_t = P_t \perp \langle t+1,\ t+1,\ t+1,\ t+1\rangle \perp
\bigoplus_{j=t+1}^{2t+1} \langle j\rangle
```

therefore represents every Fibonacci number except $t$. Its rank grows with
$t$, so Lean keeps the rank as a parameter instead of writing the form out.

## Documentation

- [docs/PAPER_CORRESPONDENCE.md](docs/PAPER_CORRESPONDENCE.md) lists, section
  by section, every place where the Lean proof argues differently from the
  manuscript, and every finite check in the proof.
- [docs/READING_GUIDE.md](docs/READING_GUIDE.md) maps the results of the
  manuscript to Lean modules.
- [docs/STATUS.md](docs/STATUS.md) says what is proven, which checks the
  workflow enforces, and how to reproduce them.
- [docs/PROVENANCE.md](docs/PROVENANCE.md) gives the sources of the explicit
  data: the transfer matrices, the witnesses, and the tables.

**Manuscript.** Scott Duke Kominers, *A Fibonacci Analogue of the Fifteen
Theorem*, [hexagon:2611.00357v1](https://hexagonmath.org/2611.00357v1).

## Build

Install Lean following the
[official instructions](https://lean-lang.org/install/). The `lean-toolchain`
file selects Lean 4.35.0, and `lake-manifest.json` pins Mathlib, atlas-lean,
TauCeti, and their dependencies.

```sh
lake exe cache get
lake build
```

Besides the build, the GitHub Actions workflow runs the linter, replays every
module in the Lean kernel with `leanchecker`, and audits the axioms: only
`propext`, `Classical.choice`, and `Quot.sound` are allowed.
[docs/STATUS.md](docs/STATUS.md) gives the commands for all four checks.

## Versions

Releases are tagged with the Fibonacci numbers in order: `v1`, `v2`, `v3`,
`v5`, `v8`, and so on. `v1` is the version that the manuscript describes.
