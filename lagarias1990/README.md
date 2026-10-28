# Lagarias 1990 in Lean 4

J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arithmetica 56 (1990), 33–53
([PDF, ICM](http://matwbn.icm.edu.pl/ksiazki/aa/aa56/aa5614.pdf), [EuDML 206298](https://eudml.org/doc/206298),
MR 91i:11024, DOI [10.4064/aa-56-1-33-53](https://doi.org/10.4064/aa-56-1-33-53)).

> **What this is.** A formalisation of a classical paper from 1990. It proves nothing new about Collatz cycles.
> The statements follow the paper, repaired where we found that the printed statement or proof has a slip; the
> repairs are listed below, next to what is printed, and the list of slips is not exhaustive. Several statements
> go beyond the printed text, for example `bseq_inj` (cited by the paper from [10]), `no3` and `min_pm1` (used
> without proof), `thm3_1_65` (Theorem 3.1 without hypothesis, constant 6/5), `thm3_2` without the prime number
> theorem, the minimality of the two corrected rows of Table 3.1, an explicit constant for (2.6) (`c = 2`, from the proof), Theorem 4.2's
> printed constant `2n⁴` by a sharper estimate than the printed proof, and the `…_printed_false` counterexamples.

**Status (2026-10-20).**
- **Kernel-checked:**
  - Section 2: Theorem 2.1, Corollaries 2.1a–b and the facts around them, the count (2.4)–(2.6) of irreducible
    cycles;
  - Section 3: the `3x+k` maps, the bijection with rational cycles, Theorems 3.1, 3.2, 3.4 and 3.5;
  - Theorems 4.1 and 4.2 (4.2 with the printed constant `2n⁴`);
  - Tables 2.1 and 2.2; Table 3.1 as described below (48 printed rows, 2 corrected rows).
- **Named hypotheses:** Theorem 3.1 with the printed constant uses the prime number theorem, and Theorem 3.2 uses
  Baker–Fel'dman. Both enter as **named hypotheses**, never as axioms. Theorem 3.1 is also proved **without any
  hypothesis**, with the constant 6/5 instead of 5/4.
- **All 60 frozen statements are proved** (`check.sh` checks that there are 61 axiom reports, one per theorem).
- **Out of scope:** Theorems 3.3 and 4.3; the bounds (4.12)–(4.14) of §4.2; Remarks (2)–(4) of p. 52 with (4.19);
  the flat segment of Fig. 4.1. Each is listed below with its reason. The minimality of the 48 unchanged rows of
  Table 3.1 is checked numerically, not in Lean.

In numbers:
- **60 frozen statements, all proved** (61 theorems: Corollary 2.1a is proved twice). The six `*_Enonces.lean`
  files define 62 `Prop`s; two of them are the named hypotheses `H_PNT` and `H_BF`. Each statement `X` is checked by
  `example : X := X_thm` in `Lagarias/Axiomes.lean`, except `cor2_1a`, checked twice by its two proofs
  (`cor2_1a_coppersmith`, `cor2_1a_lagarias`).
- **Statements before proofs.** Each statement was written in a `*_Enonces.lean` file before its proof. Git shows
  this order only for the six statements proved last ((2.4), (2.5), Table 2.1, Theorem 4.2 with `2n⁴`, (2.6),
  `eq4_4_attained`); in phases 2a and 2b, statements and proofs were committed together, including the three
  addenda of the first review (commit 4513452).
- **0 `sorry`** in the proofs (one unused marker in a copied dependency, see *Dependencies*).
- **0 `native_decide`:** table computations use `decide +kernel`.
- **Axioms:** only `propext`, `Classical.choice`, `Quot.sound` (log in [`axioms/`](axioms/)).
- **Lean 4.34.0, Mathlib v4.34.0**, i.e. after the fix of the kernel soundness bug
  [lean4#14576](https://github.com/leanprover/lean4/issues/14576) (v4.32.2).

## How to check

From the root of a clone of a release tag, or of its Zenodo archive (prerequisites and disk space: [*Re-checking the
formalisations of classical papers*](../README.md#re-checking-the-formalisations-of-classical-papers-added-2026-10-28) in the root README):

```bash
cd lagarias1990
lake exe cache get
./check.sh
```

`check.sh` first checks the sources against `SHA256SUMS`, then compiles the files one by one with
`lake env lean`, in dependency order. It then reads the `#print axioms` output of `Lagarias/Axiomes.lean`, and
fails if any theorem depends on an axiom other than the three above, or if the number of reports is not 61. It was run from a clean build on 2026-10-20 (25 files, about 6 minutes on an M1 Pro once Mathlib is cached).
*(Note of 2026-10-28: re-run from a fresh clone of tag v1.4 on an M1 Pro busy with other jobs, it took about
22 minutes, `lake exe cache get` included, each file loading Mathlib; the 61 reports were identical to `axioms/`.)*

## Named hypotheses

| name | content | source |
|---|---|---|
| `H_PNT` | `θ(x)/x → 1` (Chebyshev's `θ` of Mathlib) | the prime number theorem, which Lagarias uses as `log[1,k] = k + o(k)` (Hardy–Wright Thm 434); it is not in Mathlib v4.34 |
| `H_BF` | `∃ c₁, ∀ n ≥ 2, ∀ l, ½·n^{−c₁}·2ⁿ ≤ |2ⁿ − 3^l|`, i.e. (3.3) | a consequence of the Baker–Fel'dman bound on linear forms in logarithms (Baker 1975, Thm 3.1) |

They appear only as hypotheses of `thm3_1` (`H_PNT → …`) and `thm3_2` (`H_BF → …`).

## Layout

| file | content |
|---|---|
| `Lagarias/L1990_Enonces.lean`, `L1990b_Enonces.lean`, `Tables_Enonces.lean`, `Addenda_Enonces.lean`, `Addenda2_Enonces.lean`, `Addenda3_Enonces.lean` | frozen statements, each with a line-by-line comparison with the paper in its header (a few header rows and docstrings are superseded, see below) |
| `Lagarias/L2_Preuves.lean`, `L3_Preuves.lean`, `L4_Preuves.lean`, `Tables.lean` | phase 2a proofs (Sections 2, 3, 4, tables) |
| `Lagarias/L3b_Preuves.lean`, `L4b_Preuves.lean` | phase 2b proofs (Theorems 3.1–3.2, Ash's bound, Theorem 4.2) |
| `Lagarias/Mots.lean` | primitive words: rotation periods closed under `gcd` (Mathlib has `List.HasPeriod.gcd` for linear periods and `Function.IsPeriodicPt.gcd` for iterated maps; `rot_gcd` is proved directly here), unique irreducible root, free action of the rotations |
| `Lagarias/L2b_Preuves.lean`, `L4c_Preuves.lean` | phase 2c proofs ((2.4), (2.5), Table 2.1; Theorem 4.2 with `2n⁴`) |
| `Lagarias/Addenda.lean` | three points raised by the first adversarial review (see below) |
| `Lagarias/Addenda2.lean` | (2.6), added during the adversarial passes before release |
| `Lagarias/Addenda3.lean` | the attainment in (4.4), added during the adversarial passes before release |
| `checks/` | Python recomputations of the numerical points (not proofs; see `checks/README.md`) |
| `Lagarias/Axiomes.lean` | statement checks and `#print axioms` |
| `Labo/*`, `OneObstruction/*` | copied from `hh1997/` (see *Dependencies*) |

## The paper, result by result

| paper | Lean | status |
|---|---|---|
| (2.1)/(1.2) | `xv`, `eq2_1` | proved |
| Theorem 2.1 | `thm2_1` | proved: `x(v) ∈ Q_(2)`, `T^n x(v) = x(v)`, the parity word of `x(v)` is `v`, uniqueness |
| (1.3) | `eq1_3` | proved, both directions; `x = 0` is excluded (empty sum) |
| Corollary 2.1a | `cor2_1a`, `cor2_1a_words` | proved twice: Lagarias's proof through Theorem 2.1 and Coppersmith's 2-adic proof |
| p. 37, `2⁴ + 3 = 2² + 2·3 + 3² = 19` | `ex_p37` | proved |
| p. 39, common denominator of a cycle | `den_cycle`, `delta_eq` | proved |
| p. 37, eventually periodic or divergent | `dichotomy` | proved |
| p. 38, the parity map is one-to-one on `Q_(2)` | `bseq_inj` | proved here (the paper cites [10]) |
| Corollary 2.1b | `cor2_1b` | proved |
| (2.4) `Σ_{d∣n} d·I(d) = 2ⁿ` | `eq2_4` | proved: every word of length `n` is `u^{n/d}` for exactly one irreducible `u` of length `d ∣ n` (`sum_card_Irr`), and the rotations act freely on irreducible words, so `d` divides their number (`dvd_card_Irr`). The empty word is vacuously irreducible; (2.4) only uses `d ≥ 1` |
| (2.5) `I(n) = (1/n) Σ_{d∣n} μ(d) 2^{n/d}` | `eq2_5` | proved (Möbius inversion of Mathlib), as `n·I(n) = Σ_{d∣n} μ(d) 2^{n/d}` in `ℤ` |
| Table 2.1 | `table2_1` | proved: the 20 printed values are right. They are computed by the recursion `I(n) = (2ⁿ − Σ_{d∣n, d<n} d·I(d))/n` given by (2.4), checked by `decide +kernel` |
| (2.6) `I(n) = 2ⁿ/n + O(2^{n/2})` | `eq2_6` | proved. The frozen statement has `∃ c`; the proof gives `c = 2`, through the lemma `eq2_6_explicit` (not frozen): `0 ≤ 2ⁿ − n·I(n) < 2^{⌊n/2⌋+1}` |
| Table 2.2 | `table2_2_values`, `table2_2_complete`, `table2_2_gcd` | proved: the 23 rows, completeness for `n ≤ 6`, the `110000` remark |
| p. 40, clearing denominators; `T_{dk'}(dn') = d·T_{k'}(n')` | `clear_den`, `tk_scale` | proved |
| p. 40, rational cycles ↔ primitive cycles of the `T_k`, `k > 0`, `k ≡ ±1 (6)` | `bij3` | proved as a bijection of points (`Set.BijOn`): the elements `x` of rational cycles (odd denominator) ↔ the pairs `(k, n0)` with `n0` in a primitive cycle of `T_k`, by `x ↦ (den x, num x)` |
| p. 44, the smallest member of a primitive cycle is `≡ ±1 (6)` (used, not proved in the paper) | `no3`, `min_pm1` | `no3` (no nonzero member of a cycle of `T_k`, `3 ∤ k`, is divisible by 3) holds for every cycle; `min_pm1` (the smallest member is `≡ ±1 (6)`) is proved for positive cycles, and is false for some negative cycles (for example `{−5, −7, −10}`), see below |
| Theorem 3.1 | `thm3_1` (`H_PNT`), `thm3_1_65` | proved: with `5/4` under `H_PNT`; with `6/5` unconditionally (Chebyshev's bound `θ(n) ≥ n log 2 − O(√n log n)` of Mathlib). The proof runs over the primes `p ≥ 5`, so the `k` found are primes |
| proof of Thm 3.1: `k ∣ 2ⁿ − 3^l`; `S(t) ≤ 3^{t(t+1)(2t+1)/6}` | `k_dvd_D`, `S31_bound` | proved |
| Theorem 3.2 | `thm3_2` (`H_BF`) | proved, with `log₂` and `|D(v)|`, from `thm3_1_65` (so without `H_PNT`) |
| Theorem 3.4 | `thm3_4` | proved as printed (the first claim for every positive `n0`, even ones included); the printed proof needs `N(v)` odd, see below |
| pp. 44–45, the examples `1/(2^m − 3)` and `5/(2^m − 9)` | `ex_10m`, `ex_5` | proved, with `v` of total length `m` |
| (3.8) | `eq3_8` | proved |
| (3.9) `N(v) ≥ 3^l − 2^l` | `C_ge` (a lemma of `L3_Preuves.lean`, not a frozen statement) | proved, as a step of `eq3_8` |
| Theorem 3.5 | `thm3_5` | proved |
| (4.4), (4.5), (4.8) | `eq4_4`, `eq4_4_attained`, `eq4_5`, `eq4_8` | proved ((4.4) with the exponent repaired). `eq4_4` gives the identity and the bound `N(v) ≤ 3ⁿ − 2ⁿ`; `eq4_4_attained` gives `N(1ⁿ) = 3ⁿ − 2ⁿ`, so `3ⁿ − 2ⁿ` is the maximum element of `Σ_n` |
| Theorem 4.1 | `thm4_1`, `thm4_1_core`, `thm4_1_printed_step_m1` | proved |
| Ash, Lemma 4.7.2 | `ash_tail` | proved (Chernoff's argument) |
| Theorem 4.2 | `thm4_2_printed`, `thm4_2` | proved with the printed constant `2n⁴`, and with the constant `4n⁴` that the printed proof gives (see below) |
| Table 3.1 | `table3_1_rows`, `table3_1_row35`, `table3_1_row73` | the 48 printed `n0` are in primitive cycles of the printed length (their minimality is confirmed numerically, not in Lean); the 2 other rows are corrected, with minimality in Lean |
| Theorem 3.3 | — (`thm3_3_count_printed_false` for one step of its proof) | **out of scope**: asymptotic; it needs Baker's bound (3.3) and the divisor bound `d(B) ≤ B^{c/log log B}` (Hardy–Wright Thm 317) |
| (4.12) (pp. 50–51): `Φ(x, β log x)` against `Σ_{n ≤ β log x} I(n)`, printed with `=`; p. 51: "The bound (4.12) is exact for `0 < β ≤ φ`" | — | **out of scope**: it counts the primitive cycles of all `T_k`, `k ≤ x`, by their length, through the bijection `bij3`; this count is not formalised |
| (4.13) (p. 51) | — | **out of scope**: its first inequality follows from (4.12) and (2.6); (2.6) is proved (`eq2_6`), (4.12) is not formalised. Its second inequality is false as printed for `β ≤ 1`, see below |
| (4.14) (p. 51) | — | **out of scope**: only sketched in the paper ("one can show", arguing as in [10], Theorem D) |
| Theorem 4.3 (p. 51), Remark (4)/(4.19) (p. 52) | — | **out of scope**: asymptotic; they need Baker's bound (3.3) and the divisor bound |
| Remark (2) (p. 52) | — | **out of scope**: a variant of the constant of Theorem 4.3, through a sharper divisor bound |
| Remark (3) (p. 52) | — | **out of scope**: a conditional claim (Equidistribution Conjecture ⇒ `Φ(x, β log x) ≤ C(β, ε) x^{1+ε}`), no proof given |
| Remark (1) (p. 52) | — | a comment on the proof of Theorem 4.3, not a statement |
| Fig. 4.1 (the flat segment) | — | out of scope: the paper omits the proof |
| the conjectures (§3.1, Conjecture P, Equidistribution) and the heuristic of §3.5 | — | not theorems |

## What is printed, what is wrong, what is proved

The slips below are the ones we found; the list is not exhaustive. They are in three groups, by how they are
checked:
- **A**, the table: each row is backed by a Lean theorem, kernel-checked (a counterexample to the printed text, or
  the repaired statement), and sometimes also by a script of `checks/`;
- **B**: recomputed by a Python script of `checks/` (with its recorded output), not by Lean;
- **C**: noted on reading the page image, checked neither by Lean nor by a script.

Scripts are cited by short names: `audit` = `checks/L1990_audit_numerique.py`, `table31_details` =
`checks/L1990_table31_details.py`, `rt2`, `rt3`, `rt4` = `checks/L1990_rt2_eq413_fenetres.py`,
`checks/L1990_rt3_eq413_terme_suivant.py`, `checks/L1990_rt4_verifications.py`.

The list was read by adversarial reviews. Two were made during the formalisation: the first corrected three rows
(pp. 39, 44 and 48; the three Lean statements are frozen in `Lagarias/Addenda_Enonces.lean` and proved in
`Lagarias/Addenda.lean`), the second added a precision to the row of pp. 48–50; these rows are marked *review*.
Several adversarial passes followed before release; they led to (2.6) (`Lagarias/Addenda2.lean`), to the
attainment in (4.4) (`Lagarias/Addenda3.lean`) and to the section *Superseded header rows and docstrings*. The
release is made only after two consecutive passes with no remark. As far as we checked, none of these points is reported in
print: entry 108 of Lagarias's annotated bibliography *The 3x+1 problem: an annotated bibliography (1963–1999)*
(arXiv math/0309224) lists no erratum, and the second one, *(2000–2009)* (arXiv math/0608208), does not mention
the paper. **Added (2026-10-21):** two of these points were, however, reported online: the OEIS entry A102284 states
that the rows k = 35 and k = 73 of Table 3.1 are incorrect ("But there are errors - a(12)[k=35] and a(25)[k=73] are
incorrect."), and A102280 and A102284, which reproduce that table, give the corrected values (G. H. Morley,
14 March 2013). A note (21 October 2026) lists the slips of this paper and of Halbeisen–Hungerbühler 1997 that are
checked by a Lean theorem or by a script: doi:[10.5281/zenodo.23535498](https://doi.org/10.5281/zenodo.23535498).

**A. Backed by Lean.**

| page | printed | what is wrong | Lean (and `checks/`) |
|---|---|---|---|
| 37 | proof of Cor. 2.1a: `x(v) = (2ⁿ − 3^k)^{−1} Σ …` | the sum has `k+1` terms, so the word has `k+1` ones and the denominator is `2ⁿ − 3^{k+1}` | `eq1_3`; `checks/` (`rt4`, P3) |
| 39 | `δ(v) = D(v)/(N(v), D(v))` | negative when `D(v) < 0`: `v = 1` gives `D = −1`, `δ = −1`, while `x(v) = −1` has denominator 1 | `delta_eq` (with `|D(v)|`); `checks/` (`rt4`, P4) |
| 39 | "`T` does not change the denominator" | ambiguous (*review*): true for the formal denominator `q` of `a/q`, false for the reduced one, since `T(1/3) = 1` | `den_formal`, `den_printed_false`; the conclusion `den_cycle` holds |
| 40 | `(D(v), 6) = 1` | `v = 00` gives `D = 3` | `D6_printed_false`; `D6` (when `v` has a 1) |
| 40 | `T_k(n) = T_{−k}(−n)` | `T_1(1) = 2`, but `T_{−1}(−1) = −2` | `tk_sign_printed_false`; `tk_sign`: `T_k(n) = −T_{−k}(−n)` |
| 40 | `T_k(Z(d,k)) ⊆ Z(d,k)` (`k` odd) | `T_9(1) = 6`, `(6,9) = 3`; it needs `3 ∤ k`, which the next paragraph assumes | `tk_Z_printed_false`; `tk_Z` with `3 ∤ k` |
| 41 | Table 3.1, `k = 35`: `(7, 3)` | `{7, 28, 14}` is not primitive | `table3_1_row35`: `(13, 8)` |
| 41 | Table 3.1, `k = 73`: `(19, 60)` | `5` is in a primitive cycle of length 12 | `table3_1_row73`: `(5, 12)` |
| 41 | "for `n = 85, 107, 139` this is at least `⅓·2ⁿ`" (about `min_l |2ⁿ − 3^l|`) | these are the `k`'s; at the periods `100, 106, 136` the bound fails | `p41` |
| 43 | proof of Thm 3.3: "at least `n^{−1}C(2n,n)` distinct primitive cycles associated to such `v`" | for `n = 1` there is one cycle, not two; the number is about `C(2n,n)/(2n)` (`checks/`: computed for `n ≤ 5` and `n = 10, 20, 40`; it approaches ½) | `thm3_3_count_printed_false` (`n = 1`) |
| 44 | "we may index primitive cycles by their smallest member `n0`. This will always be an integer `n0 ≡ ±1 (mod 6)`" | true for positive cycles; false for some negative cycles if "smallest" is the minimum (*review*): `{−5, −7, −10}` has minimum `−10 ≡ 2` | `min_pm1`; `min_neg_printed_false` |
| 44 | proof of Thm 3.4: `p = ord_{N(v)}(2)` | undefined when `N(v)` is even: `v = 001` gives `x(v) = 4/5`, `N(v) = 4`, and `4` is in a primitive cycle of `T_5`; the statement covers even `n0` | `thm3_4`, as printed: the proof uses the odd part of `N(v)`; `checks/` (`rt4`, P5) |
| 44–45 | `v = 10^m`, `v = 1²0^m` | `v` must have total length `m`; read literally, the condition becomes `m ≢ 0 (mod 4)` | `ex_10m`, `ex_5`; `checks/` (`audit`, P8) |
| 47 | (4.4) `Σ 2^j 3^{n−j} = 3ⁿ − 2ⁿ` | the sum is `3(3ⁿ − 2ⁿ)` | `eq4_4_printed_false`; `eq4_4` (exponent `n−1−j`) |
| 48 | proof of Thm 4.1: "at most `m` choices", `F ≤ m·2^{n−m}` | (*review*) the count is right for `m ≥ 1`; the bound fails for `m = 0` (`M = 2`; `M = 1` is excluded by `α > 0` in the paper, the Lean `thm4_1` allows it) | `thm4_1_printed_step_m1`; `thm4_1_printed_step_false` (`M = 2`); the final bound `thm4_1` |
| 48–50 | Thm 4.2: `F ≤ 2n⁴·2^{(1−α)n}`; the printed proof ends with `4n⁴` (p. 50) | (*review*) the statement is right. The printed count of normal vectors is `(n−m)(m)·2^{n−m}`. For fixed `w`, `w̿` and class, there can be `m+1` normal windows, not `m`: in the range `2n²·2^m ≤ M < 4n²·2^m` of the proof, without using `α ≤ α_c`, `n = 6`, `M = 227`, `m = 1`, `w = 11111` gives 2 (`checks/`, `rt2`). The Lean count is `(n−m+1)(m+1)·2^{n−m}` (window positions `0 ≤ l ≤ n−m`, one window per weight `0…m`); the arithmetic–geometric mean bound `(n−m+1)(m+1) ≤ (n+2)²/4` gives `n²(n+2)² + n ≤ 2n⁴` for `n ≥ 5` (`n ≤ 4` is trivial), with the paper's choice of `m` | `thm4_2_printed` (`2n⁴`); `thm4_2` (`4n⁴`) |

**B. Recomputed by a script of `checks/`.**
- p. 34: "`k ≡ 1 (mod 6)`" should read `±1`: `x(100) = 1/5`, a primitive cycle of `T_5` (`rt4`, P6).
- p. 44: `k_m = (2^m − 3^l)/G_0` should read `2^{n+m}`: for `v = 100`, `m = 4`, `x(v0^m) = 1/125` (`rt4`, P2).
- p. 44: "`T_k(n_0) = (3n_0 + k_m)/2 ≥ k_m/2 ≥ (2^{5n} − 2ⁿ)/(3ⁿ − 2ⁿ)`": read `T_{k_m}`. The inequality holds
  (`n ≤ 14`, `m = 4n`: 26 419 words, no failure; `rt4`, P1); its reason, `2G_0 ≤ 3ⁿ − 2ⁿ` since `G_0` divides
  `2ⁿ − 3^l`, is not printed.
- pp. 49 and 51: `H(φ) ≐ 0.949955` is truncated: `H(φ) = 0.9499555…` (`table31_details`).
- p. 50: `α_c ≅ 0.0476598` is computed with the printed `H(φ)`, which gives `0.04765986…`; the value is
  `0.0476594` (the `0.04766` of p. 48 is right) (`table31_details`, `audit`).
- p. 35: `β_c ≐ 1.050005`; p. 51: `β_c = 1/(1 − α_c) ≐ 1.050005`; the value is `1.050044` (`= 2 − H(φ)`) (`audit`).
- p. 51, (4.13): the second inequality, `Σ_{n ≤ β log x} 2ⁿ/n + O(…) ≤ 2x^β/log₂ x + O(x^{β/2})` (log = log₂). Along
  `x` with `β log₂ x ∈ ℤ`, the sum is `~ 2x^β/(β log₂ x)`, with a correction of order `x^β/(log x)²`; so no bound
  `2x^β/log₂ x + O(x^{β/2})` holds for `β ≤ 1` (for `β = 1/2`, `x = 2^{100}`, the sum is 2.04 times the printed main
  term). For `β = 11/10` and `2` the printed inequality holds at the points tested (`rt2`, `rt3`).

**C. Noted on reading, not checked.**
- p. 34: "for `1 ≤ i ≤ n`" should read `0 ≤ i ≤ n − 1`.
- p. 40: "described in Section 3.6": the heuristic is in Section 3.5, the last one of Section 3.
- p. 41: "given by (3.1)" should read (2.1).
- p. 42, proof of Thm 3.1: "if all `T_l` for `k0 ≤ l ≤ k` have a primitive cycle of length `≤ t`" … The range
  includes the even `l`, where `T_l` is not defined, and the `l` with `3 ∣ l`, which have no primitive cycle; the
  contraposition may yield such an `l`. `thm3_1` and `thm3_1_65` run the argument over the primes `p ≥ 5`.
- p. 42, (3.2) `k ≤ (log D(v))³`: the proof gives it with `log₂` and `|D(v)|`, as in `thm3_2`.
- p. 43, proof of Thm 3.3: the vectors have length `2n`, so "(with period dividing `n`)" should read `2n`; Theorem 4.1
  is quoted for `v ∈ {0,1}ⁿ` with `2n²2ⁿ/M^φ`, while (4.3b) has the constant `2n`; "there are `n+1` choices of `l`"
  should read `2n+1`.
- p. 43, (3.5): the middle term is less than `4ⁿ/n`, below the printed right side `2^{2n − c_0/log log n}` for large `n`.
- p. 44: "the smallest `p ≥ 2` with `2^p ≡ 1 (mod N(v))`" differs from `ord_{N(v)}(2)` when `N(v) = 1`.
- p. 45: "if `x(v) ≤ 0`" should read `< 0`; `a(l)` should read `a(l−1)`.
- p. 46 (heuristic of §3.5): "`(|Σ_{n,l}|/D_{n,l})ⁿ ≤ (0.99)^{−n²}`": the exponent should be `n²`, with a factor
  `n^{c_1 n}`.
- p. 47: "`0 ≤ M ≤ n`" should read `0 ≤ l ≤ n`.
- p. 49, proof of Thm 4.2: the bound on `|Ω|` sums `m + 1` terms (`l = 0…m`) and bounds them by `m` times the
  largest; the `l` found just above satisfies `l ≤ m − 1`.
- p. 50: (4.12) is printed with `=`; p. 51 calls it a bound, "exact for `0 < β ≤ φ`".
- p. 50: "The flat segment between `α_c` and 1" does not match the range of `α` given in the same sentence, which
  ends at `(log₂ 3)α_c`.
- p. 51: `F₀(βn, M) ≤ (βn)⁴2^{βn}/M` omits the constant of Theorem 4.2.
- pp. 35 and 52: the bound of the introduction has `(β log k)⁶`, (4.19) has `⁵`.

## Superseded header rows and docstrings

The headers and docstrings of the frozen files compare each statement with the paper. They are frozen with the
statements (their SHA-256 are fixed), so the reviews could not edit them; the rows below are superseded by this
README. Two rows concern proof files (`Mots.lean`, `Tables.lean`), which were not edited.

| file, row or docstring | it says | read instead |
|---|---|---|
| `L1990_Enonces.lean`, p. 39 "T does not change the denominator" | FALSE (`T(1/3) = 1`) | ambiguous: true for the formal denominator (`den_formal`), false for the reduced one (`den_printed_false`) |
| `L1990_Enonces.lean`, p. 39 `v = 110000` | "the only row with `D ≠ δ`", as if printed | the paper says "Table 2.2 includes one example"; that it is the only row with `|D| ≠ δ` is what `table2_2_gcd` proves |
| `L1990_Enonces.lean`, p. 44, smallest member `≡ ±1 (6)` | "the cycle `{0}` excluded" | `min_pm1` assumes `0 < n`, i.e. positive cycles; the printed claim is false for some negative cycles, for example `{−5, −7, −10}` (`min_neg_printed_false`) |
| `L1990_Enonces.lean`, Thm 3.4 | "the first claim also covers EVEN `n0`" | the printed statement already covers them; only the printed proof does not |
| `L1990_Enonces.lean`, proof of Thm 4.1 | "`m + 1` choices" | the printed count `m` is right for `m ≥ 1` (`thm4_1_printed_step_m1`); it fails only for `m = 0`, i.e. `M ∈ {1, 2}`; the Lean core uses `m + 1` |
| `Addenda_Enonces.lean`, proof of Thm 4.1 | "fails only for `m = 0` (`M = 2`…)" | `m = 0` means `M ∈ {1, 2}`; `M = 1` is excluded by `α > 0` in the paper, and the Lean `thm4_1` allows it |
| `L1990_Enonces.lean`, docstring of `den_printed_false` | "printed reason … — false" | ambiguous: false for the reduced denominator (what `den_printed_false` proves), true for the formal one (`den_formal`) |
| `L1990_Enonces.lean`, `ex_5` (header row and docstring) | p. 45: "primitive iff `m ≢ 2 (4)`" | the paper says "provided `m ≢ 2 (mod 4)`", a sufficient condition; `ex_5` proves the equivalence, more than printed |
| `L1990_Enonces.lean`, docstring of `thm4_1_core` | "repaired count `m + 1`" | not a repair: the printed count `m` is right for `m ≥ 1` (`thm4_1_printed_step_m1`); `thm4_1_core` uses `m + 1`, which also covers `m = 0` |
| `L1990_Enonces.lean`, docstring of `table2_2_gcd` | "it is the only row of Table 2.2 with `(N(v), D(v)) > 1`" | this is proved here, not printed: the paper says "Table 2.2 includes one example" |
| `L1990_Enonces.lean`, p. 39, `den_cycle` | "none (the conclusion holds; the printed reason does not)" | the printed reason is ambiguous, not false: it holds for the formal denominator (`den_formal`); the conclusion holds (`den_cycle`) |
| `Mots.lean`, header (not frozen, left unchanged) | "Mathlib v4.34 has neither primitive words, nor Lyndon words, nor necklaces" | Mathlib v4.34 has `Cycle` (lists up to rotation) but neither primitive nor Lyndon words, nor their count |
| `Tables.lean`, header (not frozen, left unchanged) | "All computations are checked by the kernel (`decide +kernel`)" | a few steps use plain `decide`, also checked by the kernel; no `native_decide` |
| `Tables_Enonces.lean`, header | "kernel computation, `decide +kernel`" | same remark: a few proof steps in `Tables.lean` use plain `decide` |
| `L1990_Enonces.lean`, header row and docstring of `eq3_8` | "(3.8)–(3.9)" | `eq3_8` states (3.8) with its equality case; (3.9) is the lemma `C_ge` |
| `L1990b_Enonces.lean`, list of proof files | `L3b_Preuves`, `L4b_Preuves`, `L2b_Preuves` | also `L4c_Preuves.lean` (`thm4_2_printed`) and `Mots.lean` |
| `Addenda2_Enonces.lean`, first line | "the second adversarial review" | the first adversarial pass before release |
| `L1990_Enonces.lean`, docstring of `eq4_4` | "the maximum element of `Σ_n`" | `eq4_4` proves the identity and the bound `N(v) ≤ 3ⁿ − 2ⁿ`; the attainment is `eq4_4_attained` (`Addenda3_Enonces.lean`) |
| `L1990b_Enonces.lean`, Ash's bound | `Σ_{j ≥ αk}` | the printed sum is over `j > αk`; the Lean sum has more terms, so `ash_tail` is a slightly stronger statement |
| `L1990b_Enonces.lean`, Thm 3.1 | the printed range includes `l` with `3 ∣ l`; the contraposition "can only produce such an `l`" | the range also includes the even `l`, where `T_l` is not defined; the contraposition may yield such an `l` (it is not forced to) |

## Related work

- **Böhm–Sontacchi.** Lagarias says Theorem 2.1 is "essentially due to Böhm and Sontacchi". Their paper is
  formalised in Lean ([tcosmo/BohmSontacchi1978_lean](https://github.com/tcosmo/BohmSontacchi1978_lean), listed
  on ccchallenge as formalised, status `audited`). Its Proposition 5 is the integer version: a nonzero integer is
  a cycle point iff it is `sum/(2ⁿ − 3^m)` for a valid schedule.
- **Halbeisen–Hungerbühler 1997.** The rational version for every parity word is their Lemma 2 (they attribute it
  to Lagarias); it is in this repository's `hh1997/`, with the unique fixed point (`lemma2_fixed`) and the parity
  word (`lemma2_cycle`). `thm2_1` restates it in Lagarias's form.
- **Belaga–Mignotte**, *Experimental Math.* 7 (1998) 145–151, has close counterparts of several results here:
  - Lemma 3.5(2) (injectivity, "observed many times—for example, in [Lagarias 1990]") ↔ `cor2_1a`;
  - Proposition 3.6 (it "generalizes the results … of [Böhm and Sontacchi 1978] and of [Lagarias 1990,
    Theorem 2.1]") ↔ `thm2_1`, `bij3`;
  - Proposition 3.7 ↔ the irreducible words;
  - Proposition 3.11 (a cycle through `n = A_k` for `d = 2^{p_k} − 3^k`, where `A_k` does not depend on `p_k`),
    with `p_k` varying ↔ the construction in `thm3_4` (`v` followed by zeros);
  - Remark 3.13 (`d = Q(2^{p_k} − 3^k)`, `n = Q·A_k`) ↔ the scaling `tk_scale`, `clear_den`.
- **Earlier formalisations.** We found none of Lagarias 1990 (ccchallenge entry `Lagarias1990`: not started on
  2026-10-20). (Update 2026-10-28: ccchallenge record 15 of that entry, created on 2026-10-20 after that check, is
  this formalisation; it points to the Zenodo DOI of release v1.1, 10.5281/zenodo.23514572.)

## Dependencies

Six files are copied unchanged from `hh1997/` (commit 36d5136; same SHA-256 as in `hh1997/SHA256SUMS`):

| file | sha256 |
|---|---|
| `Labo/Blueprint.lean` | `c397d06ecff993125417ea28750cd82d24dc31461de6bfa15435082d49c185ac` |
| `Labo/S2_Pont.lean` | `a7ea2ed74d1e3f58db2982eb2be236104a6f366b83e851205a31d4a84bab4e13` |
| `Labo/HH1997_Enonces.lean` | `f168e123c636902e4967652141a3cb6df5e8f62f11c586a76a8ca48d33a9f73a` |
| `Labo/HH1997_Preuves.lean` | `1bdc2594855c719f6a810e8db25dc918f860be90dcaad36d9e785573e03b1133` |
| `OneObstruction/ContentDescent.lean` | `ae7ec6817c6a088dbe2bc180eea606147458c083c1e0576857cc71b9f6272c10` |
| `OneObstruction/TransportRecurrence.lean` | `70e52e5d31dfc890e411470f38628f39e6220e7babbdcf086bf67eeec1f4c7f6` |

They provide `N(v)` (`LaboBP.C`), `D(v)` (`LaboBP.d`), `T` on ℚ (`LaboHH.collatzQ`) and Lemma 2 of
Halbeisen–Hungerbühler. `Labo/Blueprint.lean` contains one `sorry`: the marker `Tstar_open` for the open
statement T★. It is never used; the axiom report of every theorem here excludes `sorryAx`.
