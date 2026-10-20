# One Obstruction, Three Faces — Merle Lean stack

Archived on Zenodo: https://doi.org/10.5281/zenodo.23498095 (concept DOI; v1.0 = 10.5281/zenodo.23498096).

> **Status (2026-10-02).** This is the Merle side of the joint note *One obstruction, three
> faces* with Benjamin Macindoe. It formalizes and checks entries of the shared claims ledger.
> **Nothing here excludes a Collatz cycle beyond the published bounds** (Bařina's verification
> to 2⁷¹; Hercher 2023). Every kernel claim was first checked on Lean 4.27.0, which predates the
> fix of the kernel soundness bug [lean4#14576](https://github.com/leanprover/lean4/issues/14576)
> (fixed in v4.32.2, 2026-07-28); all six files were then re-checked on Lean 4.34.0 — see
> [`recheck-v4.34/RECHECK.md`](recheck-v4.34/RECHECK.md).

The **Lean 4 verification stack** (Eric Merle's "kernel key") for the joint note
*One obstruction, three faces* with Benjamin Macindoe.

Per the collaboration protocol's three-repo model, each side's verification
stack lives in its own repository and is never merged into the other's:

- **this repo** — Merle side, the Lean kernel key;
- [`macindoe/collatz`](https://github.com/macindoe/collatz) — Macindoe side, independent code;
- the shared repo [`macindoe/one-obstruction-three-faces`](https://github.com/macindoe/one-obstruction-three-faces)
  (note text + protocol + claims ledger + correspondence rounds) links to both.

A load-bearing claim turns **both** keys — the Lean kernel here, independent
code there — with neither derived from the other. The status of each entry is the
last "Key status" block of `LEDGER.md` in the shared repo, not this README.

## Contents

| file | ledger | what is kernel-checked |
|---|---|---|
| `OneObstruction/TransportRecurrence.lean` | L-A1 | recurrence ⟹ the `p` divisibility conditions collapse to one (below) |
| `OneObstruction/ContentDescent.lean` | L-A4 | a repeated word `B^k` is a cycle iff `B` is (`cycle_iff`); the gcd climb law |
| `OneObstruction/ContentSeparation.lean` | L-A5 | the adjacent-transfer difference formulas T1/T2 and the separation corollaries |
| `OneObstruction/DeficitLemma.lean` | L-A7 | the margin inequality at the rational constant 1/13 (`marginTarget`) |
| `OneObstruction/T1Structure.lean`, `LegendreApprox.lean` | L-A8 | the forced ceiling `K = ⌈(p+1)·log₂3⌉`; the Legendre step and the 22-point discharge at `X = 2⁷¹` (windows `n ≤ 3.5032·10¹⁰`, chain; `n ≤ 4.954·10¹⁰`, direct route). Two continued-fraction facts and the multiples cancellation remain prose (LEDGER L-A8). The window lies below Hercher's published bound. |
| `recheck-v4.34/` | — | the six files above on Lean 4.34.0; `Labo/`: lab modules offered for information, no ledger entry, one `sorry` (the open target `Tstar_open`) — see `LABO.md` |
| `hh1997/` | — | Halbeisen–Hungerbühler 1997 (*Acta Arith.* 78) formalised on Lean 4.34.0: a classical paper, not a ledger entry; 70 proved statements, standard axioms; one remark of the paper not proved — see `hh1997/README.md` |
| `lagarias1990/` | — | Lagarias 1990 (*Acta Arith.* 56) formalised on Lean 4.34.0: a classical paper, not a ledger entry; 59 proved statements, standard axioms; Theorem 3.1 with the printed constant and Theorem 3.2 under named hypotheses (Theorem 3.1 also without any hypothesis, constant 6/5); Theorems 3.3 and 4.3 out of scope — see `lagarias1990/README.md` |
| `experiments/` | — | Python verification scripts and outputs (`experiments/README.md`) |
| `rounds/` | — | round 11 only; rounds 12 onward live in the shared repo |

**Two stale docstrings in `T1Structure.lean`** (kept unchanged so that the re-checked files stay
byte-identical to what was checked): the header (l. 19-20) says the direct route is "NOT yet a
theorem in this file" — it is, since `acd7063` (`log_gap_direct`, `quotient_is_convergent_direct`,
`discharge_all_direct`); the docstring of `seam_gap_at_barina` (l. 236-243) says the Legendre step
and the 22-point check are "not formalized here" — they are, further down
(`quotient_is_convergent_gen`, `discharge_all`).

## Prior literature (added 2026-10-20)

Several ledger entries verified here turned out to be classical, or anticipated in substance. The
Lean files are unchanged; this table says whom to credit. The matching notes for the shared ledger go
through the shared repository: L-A1 and L-A4 in round 20 (PR #10, under review), the others in the
next round.

| ledger | prior literature | what remains ours |
|---|---|---|
| L-A1 | Halbeisen–Hungerbühler 1997, Lemma 9, eq. (13)–(15); Seifert 1988, Theorem 1 | the Lean key (`transport_collapse`) |
| L-A4 | Halbeisen–Hungerbühler 1997, eq. (4): W₀ = (2^K − 3^n) + ϕ (bridge `W0_bridge` in [`hh1997/`](hh1997/)) | the Lean key |
| L-A5 | the invariance of the gcd under rotation: Lagarias 1990, §2; Halbeisen–Hungerbühler 1997, Lemma 9, eq. (15); Wegner 2021 ([arXiv:2101.08060](https://arxiv.org/abs/2101.08060)), eq. (16)–(18). The adjacent exchange T1/T2 is eq. (2) and (4) of Halbeisen–Hungerbühler 1997, chained | the normalisation C, the gcd corollary, the Lean key |
| L-A7 | in substance, T. Tao, [blog post of 2011-08-25](https://terrytao.wordpress.com/2011/08/25/the-collatz-conjecture-littlewood-offord-theory-and-powers-of-2-and-3/): the heuristic count 1/q per word, Baker's theorem for q, Stirling, the factor (0.9659…)^a; our c_gen = 0.0793186 = (1 − H₂(log₃ 2))·log₂ 3 is the same constant, counted per odd step | the explicit additive tail (μ named, C₀); the kernel proof at the constant 1/13 |
| L-A8 | the chain is classical: Crandall 1978 and Eliahou 1993 (product bound, window); the Legendre step as in Simons–de Weger 2005, Lemma 9(a) | re-proved in the kernel |

## Ledger entry L-A1 — the transport recurrence

`OneObstruction/TransportRecurrence.lean`.

Independent simultaneous discovery (Merle, integer form; Macindoe, fixed-point
form, `reverse.md` 14.15.9.2), joined by the seam identity `N_r + q = 2^{m_r} R_r`.
**Correction (2026-10-20): the recurrence was not new.** It is Halbeisen–Hungerbühler 1997,
Lemma 9, eq. (13)–(15), and Seifert 1988, Theorem 1 (see *Prior literature* above); what is ours
is the Lean key below. The text of this section is otherwise kept as it was.

**Certified here (kernel, 0 `sorry`, no user axioms):** from the transport
recurrence

```
2^{σ_r} · R_{r+1} = 3^{m_r} · R_r + (2^{s_r} − 1) · q ,   q = 2^K − 3^n
```

the `p` per-rotation divisibility conditions of a period-`p` cycle **collapse
to a single condition**: `q ∣ R_r ↔ q ∣ R_0` for every rotation `r`
(`transport_collapse`), equivalently `(∀ r, q ∣ R_r) ↔ q ∣ R_0`
(`cycle_divisibility_one_check`).

The modulus is the **unreduced** `q = 2^K − 3^n` (it differs from the reduced
denominator exactly when `gcd(q, R_r) > 1`, e.g. the `p = 7` seed `n = 94` has
`gcd = 7`); unit transport mod the unreduced `q` implies it mod every divisor.

**Scope, stated honestly (ARES).** The recurrence itself — the algebraic
identity that the elimination numerators `R_r` satisfy it — is *not* proved
here; it is verified numerically on both sides (29,211 checks + 60 shared
test-vectors at `macindoe/collatz`, `experiments/transport_recurrence_vectors.json`,
0 failures) and proved in fixed-point form in Macindoe `reverse.md` 14.15.9.2.
This artifact certifies the *kernel-friendly core*: recurrence ⟹ collapse. A
sanity canary (the trivial cycle, `q = 2^4 − 3^2 = 7`) is proved inside Lean to
witness that the hypothesis is non-vacuous.

## Kernel version

The files at the repository root were checked on **Lean 4.27.0 / Mathlib v4.27.0**
(rev `a3a10db`), before the fix of lean4#14576. All six were recompiled on
**Lean 4.34.0 + Mathlib v4.34.0** (post-fix) on 2026-09-23: 0 errors, 0 `sorryAx`,
40 declarations, each depending only on a subset of `[propext, Classical.choice, Quot.sound]`
(`recheck-v4.34/axioms_v4.34.txt`). Five files are byte-identical; `T1Structure.lean`
differs by its import path and two Mathlib renames.

## Reproduce

There is no `OneObstruction.lean` root file, so a bare `lake build` is not a valid target;
build the modules by name. On the post-fix kernel:

```
cd recheck-v4.34
lake exe cache get
lake build OneObstruction.LegendreApprox OneObstruction.TransportRecurrence \
  OneObstruction.ContentDescent OneObstruction.ContentSeparation \
  OneObstruction.DeficitLemma OneObstruction.T1Structure
```

Each file except `LegendreApprox.lean` ends with `#print axioms`. For L-A1 the output is the
**kernel-3** profile — no user axioms, no `native_decide`:

```
'CollatzTransport.transport_collapse' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'CollatzTransport.cycle_divisibility_one_check' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The root-level v4.27.0 files are kept as they were checked; `TransportRecurrence.lean`
also compiles alone with `lake env lean` in any Lean 4.27.0 + Mathlib project.

## Working conditions, disclosed

Research direction and standards of evidence are the author's; the mathematical
development is carried out with an AI collaborator (Claude) under the A.R.E.S.
protocol (independent second key, zero bibliographic recall, every assertion
traceable to a runnable check). The Lean kernel is the arbiter of the proofs —
not of their hypotheses, and not of a model's reading of its output: commit
`7d46474` retracts `da2c8db`, where an aborted compilation was misreported as
"0 errors"; and the kernel itself can have bugs (lean4#14576).

License: CC BY 4.0.
