# Halbeisen–Hungerbühler 1997 in Lean 4

L. Halbeisen, N. Hungerbühler, *Optimal bounds for the length of rational Collatz cycles*,
Acta Arithmetica 78 (1997), 227–239 ([PDF](https://bibliotekanauki.pl/articles/1390963.pdf),
[zbMATH 0863.11015](https://zbmath.org/0863.11015)).

Archived on Zenodo: https://doi.org/10.5281/zenodo.23498095 (concept DOI; v1.0 = 10.5281/zenodo.23498096).

> **What this is.** A formalisation of a classical paper from 1997. It proves nothing new about
> Collatz cycles: every theorem here is the paper's, sometimes in a slightly stronger form noted below.
> In particular the §5 equivalence is formalised as an equivalence; the Collatz question it restates
> stays open.

**Status (2026-10-19).** Every result that the paper proves is kernel-checked, together with the
finite verification behind the numerical example of §4.4, which the paper did partly numerically
(a Mathematica procedure in floating point). One statement of the paper is stated here and **not proved**:
`remark1_large` (Remark 1, "for l > 10³, 7/10 can be replaced by 1/2"), for which the paper gives no
proof. Two items are not formalised at all: Remark 2 (an asymptotic remark without a precise
statement) and two figures the paper quotes from other authors (Lagarias's l ≥ 301 994 and
Eliahou's k(2⁴⁰) = 17 087 915).

- **70 proved statements**, each frozen in a `*_Enonces.lean` file before its proof was written, each
  checked by `example : X := X_thm` (the proof has exactly the type of the frozen statement); one more
  frozen statement, `remark1_large`, is not proved.
- **0 `sorry`** in the proofs (one unused marker in a dependency, see *Dependencies*), **0 `native_decide`**, **axioms: only `propext`, `Classical.choice`,
  `Quot.sound`** (logs in [`axioms/`](axioms/)).
- **Lean 4.34.0, Mathlib v4.34.0** (`lean-toolchain`, `lake-manifest.json`), i.e. after the fix of the
  kernel soundness bug [lean4#14576](https://github.com/leanprover/lean4/issues/14576) (v4.32.2).

## How to check

```bash
cd hh1997
lake exe cache get
./check.sh
```

`check.sh` compiles the 33 files one by one with `lake env lean`, in dependency order, then reads the
`#print axioms` output of the nine `*_Axiomes.lean` files and fails if any theorem depends on an
axiom other than the three above (this also rules out `sorryAx` and `Lean.ofReduceBool`, the axiom
behind `native_decide`). On an M1 Pro it takes about 30 minutes, mostly loading Mathlib; no file
needs more than a few minutes. It was run from a clean copy of this folder before publication
(2026-10-19), with the result recorded in `axioms/`.

## Layout

| files | content |
|---|---|
| `Labo/HH1997_*` | batch a: (2), (3), (4), Lemma 2, Lemmas 4–5, Corollary 1, (13), Lemma 9 |
| `Labo/HH1997b_*` | batch b: Lemma 1, Lemma 3, Lemma 7, Theorem 4 |
| `Labo/HH1997c_*` | batch c: Propositions 1–2, Lemma 6, Remark 1, Lemma 1 (sign), reduction of §4.4 |
| `Labo/HH1997d_*` | batch d: Lemma 8, Theorems 1–3, continued fractions of log₂ 3, "optimal" |
| `Labo/HH1997e_*` | batch e: (A′) ⇔ ¬(A) of §5; joint check of batches a–e in one environment |
| `Labo/HH1997f_*` | batch f: the finite verification of §4.4 |
| `Labo/Blueprint.lean`, `Labo/S2_Pont.lean`, `OneObstruction/ContentDescent.lean`, `OneObstruction/TransportRecurrence.lean` | earlier files reused by batch a (see *Dependencies*) |
| `axioms/` | the `#print axioms` output of the nine `*_Axiomes.lean` files |
| `SHA256SUMS` | hashes of every `.lean` file |

In each batch, `*_Enonces.lean` holds only definitions and `def X : Prop` statements, with a
**line-by-line comparison with the paper in its header** (paper text, Lean name, deviation);
`*_Preuves.lean` holds the proofs; `*_Axiomes.lean` checks each proof against its statement and
prints its axioms.

## The paper, result by result

| paper | Lean statement(s) | status |
|---|---|---|
| (2), (3), (4) | `eq2`, `eq3`, `eq4` | proved |
| Lemma 2 (Lagarias) | `lemma2_affine`, `lemma2_fixed`, `lemma2_cycle` | proved |
| Lemma 1 (pseudo-cycles are cycles; cycles are positive or negative) | `lemma1`, `lemma1_sign`, `zero_cycle` | proved; `{0}` must be excluded from "positive or negative" |
| Lemma 3 (Abel summation) | `lemma3`, `lemma3_strong` | proved, also the stronger form used in the proof |
| Lemma 4, Lemma 5, Corollary 1 | `lemma4`, `lemma5`, `cor1` | proved |
| Proposition 1 | `prop1` | proved |
| Proposition 2 | `prop2`, `blocks23`, `blocks160` | proved for all l > 6; the block decomposition holds from l ≥ 23 (printed: 160) |
| Remark 1, 1/20 ≤ M/(n3ⁿ) ≤ 7/10 | `remark1`, `remark1_lower6` | proved, in fact with 1/6 and 2/3 |
| Remark 1, ≤ 1/2 for l > 10³ | `remark1_large` | **not proved** (no proof in the paper; numerically the maximum is 0.46 for l ≤ 3000) |
| Lemma 6 | `lemma6` | proved as printed, without the concavity the paper asserts |
| Remark 2 | — | not formalised (asymptotic, no precise statement) |
| Lemma 7 | `lemma7`, `lemma7_dom`, `lemma7_step` | proved (n ≤ l made explicit) |
| Lemma 8 (Crandall) | `lemma8`, `lemma8_gen` | proved; `lemma8_gen`: for every minimum when n ≥ 2 |
| Theorem 1 (Crandall) | `thm1`, `thm1_all_k`, `cf_gap_all`, `cf_size` | proved for every k (paper: k > 4); the needed continued-fraction facts for log₂ 3 are proved here |
| Theorem 2 (Eliahou) | `thm2`, `thm2_gen` | proved, also for every positive rational cycle |
| Theorem 3 | `thm3`, `thm3_last`, `thm3_line_of` | proved |
| Theorem 4 | `thm4`, `thm4_core`, `eq11`, `Q4_eq_M`, `nOf_spec` | proved: \|C\| ≥ L(min C) for every positive cycle in ℚ₍₂₎ |
| "optimal", read as equality | `opt_counterexample` | false in that reading: the cycle 1/5 → 4/5 → 2/5 → 1/5 has \|C\| = 3, L(1/5) = 2; "optimal" holds in the sense of the bound |
| §4.4 example | `example44`, `example44_check`, `example44_Lm`, `example44_step2`, `example44_step2_star`, `example44_step3`, `example44_A` | proved: if (C) is verified up to m = 212 366 032 807 211 (`VerifiedUpTo`, a hypothesis of the statement), every cycle in ℕ not containing 1 has at least 102 225 496 elements; and L(m) = 102 225 496 exactly |
| (13), Lemma 9 (14)–(15) | `eq13`, `lemma9_14`, `lemma9_14_gen`, `lemma9_15`, `lemma9_15_gen` | proved, also without the superfluous hypotheses |
| §5, (A′) ⇔ ¬(A) | `Aprime_equiv` | proved |

## How the §4.4 check fits in the kernel

The kernel refuses numerals above 2²⁴ bits by default, and 2^17 087 915 has 17 087 916 bits, so the
critical value M of the length 17 087 915 cannot be computed exactly. Instead:

- every length l ≥ 1 is written as l = a·p₁₆ − c·p₁₇ (p₁₆ = 17 087 915, p₁₇ = 85 137 581: numerators of
  convergents of log₂ 3, in the paper's indexing), and 2^l / 3^n(l) is bounded from below on that
  lattice; this settles all lengths except 6 by linear inequalities, without enumerating 10⁸ cases;
- the 6 exceptional words are concatenations of Christoffel words along the convergents
  (`stilde_append`, `stilde_wpow`); by (4), the bound ϕ < m(2^l − 3^n) is stable under
  concatenation (`phi_lt_append`), so only the word of length 17 087 915 needs a number;
- that number is bracketed between rationals with 128-bit denominators, each rounding checked by
  `decide +kernel` (kernel GMP arithmetic); the largest integer the kernel handles is about
  302 138 bits. The margin is small: Q4(17 087 915) = m − 0.711.

## What the formalisation found in the paper

Nothing here breaks a theorem of the paper.

- **Typos.** In ρ_l, "s₂" stands for s_{l−1}; in the proof of Lemma 5, ">" for "≥"; in Theorem 4, a
  misplaced parenthesis; in §4.4, "Lemma 1" for "Proposition 1", and p and q interchanged.
- **Missing or partial proofs.** The end of the proof of (15) is a sketch; Theorem 4 has no separate
  proof; Lemma 6 is proved only asymptotically (concavity asserted, limits that say nothing for each
  l > 160); Remark 1 has no proof; Lemma 8 and Theorems 1–2 are quoted without proof.
- **Thresholds more cautious than needed.** The block decomposition holds from l ≥ 23, not 160; the
  key inequality of Theorem 3 fails only at l = 2, 3, 4, 6, so |C| > 160 is far from tight; Theorem 1
  holds for every k; the hypotheses "s ≠ 0…0" and "2^l − 3^n > 0" of (14), and the second one of (15),
  are not needed.
- **Omissions.** The cycle {0} is neither positive nor negative; Lemma 7 assumes n ≤ l without saying
  so; k(m) is meaningless when n(k) = 0.
- **§4.4.** Six exceptional lengths suffice where the paper sets aside eight (3p₁₆ + p₁₄ and
  4p₁₆ + p₁₄, with p₁₄ = 301 994, pass the paper's own criterion: `example44_step2_star`). The First
  step bounds cycle lengths but not Q4(l) for l < p₁₆, which the Fourth step needs; the lattice
  argument above covers every l ≥ 1 directly. The example is optimal (`example44_Lm`), which the paper
  does not say.

As far as we could check (EuDML, the authors' pages, Lagarias's annotated bibliography 2003,
Cox–Ghosh–Sultanow 2021; 20 Oct 2026), none of the points above has been reported in print. Lagarias
already writes "optimal" in quotation marks (MR 98g:11025). A note (21 October 2026) lists the slips of this paper and of
Lagarias 1990 that are checked by a Lean theorem or by a script: doi:[10.5281/zenodo.23535498](https://doi.org/10.5281/zenodo.23535498).

## Dependencies

Batch a reuses four earlier files, byte-identical to the ones in [`../recheck-v4.34/`](../recheck-v4.34/)
(see `SHA256SUMS`):

- `Labo/Blueprint.lean` and `Labo/S2_Pont.lean` define the lab's word sums (`LaboBP.C`, `Csum`); the
  bridge `phi_eq_C` shows that HH's ϕ is `LaboBP.C`. **`Blueprint.lean` contains one `sorry`**: the
  marker `Tstar_open` for an open target of the lab, never used downstream. The axiom logs show that
  no theorem of this folder depends on it.
- `OneObstruction/ContentDescent.lean` and `OneObstruction/TransportRecurrence.lean` are ledger files
  of the joint note with B. Macindoe. The bridges `W0_bridge` and `eq4_kernel` show that the cocycle
  of `ContentDescent` is HH's (4) on block words; `lemma9_core` derives the core of Lemma 9 from the
  collapse `CollatzTransport.collapse_of_recurrence`. The corresponding prior-art notes for the shared
  ledger are proposed in round 20 of the shared repository, under review.

## Authorship and use of AI

Statements, proofs and this README were written by **Claude Opus 5.5** (Anthropic), in Claude Code
sessions of Eric Merle's lab on 2026-10-19; each statement was compared line by line with the paper
before its proof was written, and the whole folder was recompiled from scratch by a separate session
before publication. Numerical witnesses (Python) were run before the proofs to test predictions;
they prove nothing — the proofs are the Lean files. Responsible: Eric Merle.
