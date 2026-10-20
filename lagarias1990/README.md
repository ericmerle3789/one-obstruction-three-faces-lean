# Lagarias 1990 in Lean 4 (phase 2a)

J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arithmetica 56 (1990), 33–53
([PDF, ICM](http://matwbn.icm.edu.pl/ksiazki/aa/aa56/aa5614.pdf), [EuDML 206298](https://eudml.org/doc/206298),
MR 91i:11024).

> **What this is.** A formalisation of the elementary core of a classical paper from 1990. It proves nothing new
> about Collatz cycles: every theorem here is the paper's, sometimes repaired where the printed statement or proof
> has a slip (each repair is listed below, next to what is printed).

**Status (2026-10-20, phase 2a).** Section 2 (Theorem 2.1, Corollaries 2.1a–b and the facts around them),
the elementary part of Section 3 (the `3x+k` maps, the bijection with rational cycles, Theorems 3.4 and 3.5),
Theorem 4.1, and the tables are kernel-checked. Phase 2b (Theorem 4.2, Theorems 3.1–3.2 under named
hypotheses, (2.4)–(2.5) and Table 2.1) is in progress. Theorems 3.3 and 4.3 are **out of scope** (see below).

- **45 proved statements**, each frozen in `Lagarias/L1990_Enonces.lean` or `Lagarias/Tables_Enonces.lean` before
  its proof was written, each checked by `example : X := X_thm` in `Lagarias/Axiomes.lean`.
- **0 `sorry`** in the proofs (one unused marker in a copied dependency, see *Dependencies*), **0 `native_decide`**
  (table computations use `decide +kernel`), **axioms: only `propext`, `Classical.choice`, `Quot.sound`**
  (log in [`axioms/`](axioms/)).
- **Lean 4.34.0, Mathlib v4.34.0**, i.e. after the fix of the kernel soundness bug
  [lean4#14576](https://github.com/leanprover/lean4/issues/14576) (v4.32.2).

## How to check

```bash
cd lagarias1990
lake exe cache get
./check.sh
```

`check.sh` compiles the 13 files one by one with `lake env lean`, in dependency order, then reads the
`#print axioms` output of `Lagarias/Axiomes.lean` and fails if any theorem depends on an axiom other than the
three above. It was run from a clean build on 2026-10-20 (about 2.5 minutes on an M1 Pro once Mathlib is cached).

## Layout

| file | content |
|---|---|
| `Lagarias/L1990_Enonces.lean` | frozen statements, Sections 2–4, with a line-by-line comparison with the paper in its header |
| `Lagarias/L2_Preuves.lean` | Section 2 |
| `Lagarias/L3_Preuves.lean` | Section 3 |
| `Lagarias/L4_Preuves.lean` | Section 4 |
| `Lagarias/Tables_Enonces.lean`, `Lagarias/Tables.lean` | Tables 2.2 and 3.1, p. 41, the count in the proof of Theorem 3.3 |
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
| Table 2.2 | `table2_2_values`, `table2_2_complete`, `table2_2_gcd` | proved: the 23 rows, completeness for `n ≤ 6`, the `110000` remark |
| p. 40, clearing denominators; `T_{dk'}(dn') = d·T_{k'}(n')` | `clear_den`, `tk_scale` | proved |
| p. 40, rational cycles ↔ primitive cycles of the `T_k`, `k > 0`, `k ≡ ±1 (6)` | `bij3` | proved (`Set.BijOn`) |
| p. 44, the smallest member of a primitive cycle is `≡ ±1 (6)` (used, not proved in the paper) | `no3`, `min_pm1` | proved |
| Theorem 3.4 | `thm3_4` | proved; the first claim also for even `n0` |
| pp. 44–45, the examples `1/(2^m − 3)` and `5/(2^m − 9)` | `ex_10m`, `ex_5` | proved, with `v` of total length `m` |
| (3.8)–(3.9) | `eq3_8` | proved |
| Theorem 3.5 | `thm3_5` | proved |
| (4.5), (4.8) | `eq4_5`, `eq4_8` | proved |
| Theorem 4.1 | `thm4_1`, `thm4_1_core` | proved |
| Table 3.1 | `table3_1_rows`, `table3_1_row35`, `table3_1_row73` | 48 rows: the printed `n0` is in a primitive cycle of the printed length (minimality of `n0` not checked); the 2 other rows are corrected, with minimality |
| Theorem 4.2, Theorems 3.1–3.2, (2.4)–(2.6), Table 2.1 | — | phase 2b |
| Theorem 3.3, Theorem 4.3, (4.13)–(4.14), Remark (4)/(4.19) | — | **out of scope**: asymptotic results that need A. Baker's bound on `|2ⁿ − 3^l|` and the divisor bound `d(B) ≤ B^{c/log log B}` (Hardy–Wright Thm 317) |
| Fig. 4.1 (the flat segment) | — | out of scope: the paper omits the proof |
| the conjectures (§3.1, Conjecture P, Equidistribution) and the heuristic of §3.5 | — | not theorems |

## What is printed, what is false, what is proved

Each row was read on the page image and is checked here by the Lean kernel; the numerical ones were also
recomputed independently in Python. As far as checked, none of these points is reported in print (no erratum is
listed in Lagarias's own annotated bibliography, entry 108).

| page | printed | what is false | proved here |
|---|---|---|---|
| 37 | proof of Cor. 2.1a: `x(v) = (2ⁿ − 3^k)^{−1} Σ …` | the word has `k+1` ones | `eq1_3` (exponent `k+1`) |
| 39 | "`T` does not change the denominator" | `T(1/3) = 1` | `den_printed_false`; true statement `den_step`; the conclusion `den_cycle` holds |
| 40 | `(D(v), 6) = 1` | `v = 00`: `D = 3` | `D6_printed_false`; `D6` (when `v` has a 1) |
| 40 | `T_k(n) = T_{−k}(−n)` | `T_1(1) = 2`, `T_{−1}(−1) = −2` | `tk_sign_printed_false`; `tk_sign`: `T_k(n) = −T_{−k}(−n)` |
| 40 | `T_k(Z(d,k)) ⊆ Z(d,k)` (k odd) | `T_9(1) = 6`, `(6,9) = 3` | `tk_Z_printed_false`; `tk_Z` with `3 ∤ k` |
| 41 | Table 3.1, `k = 35`: `(7, 3)` | `{7, 28, 14}` is not primitive | `table3_1_row35`: `(13, 8)` |
| 41 | Table 3.1, `k = 73`: `(19, 60)` | `5` is in a primitive cycle of length 12 | `table3_1_row73`: `(5, 12)` |
| 41 | "for `n = 85, 107, 139`, `min_l |2ⁿ − 3^l| ≥ ⅓·2ⁿ`" | these are the `k`'s; the periods are `100, 106, 136`, where the bound fails | `p41` |
| 43 | proof of Thm 3.3: "at least `n^{−1}C(2n,n)` primitive cycles" | for `n = 1`: one cycle, not two | `thm3_3_count_printed_false` |
| 44 | proof of Thm 3.4: `p = ord_{N(v)}(2)` | undefined when `N(v)` is even (`n0` even) | `thm3_4` uses the odd part of `N(v)` |
| 44–45 | `v = 10^m`, `v = 1²0^m` | `v` must have total length `m` | `ex_10m`, `ex_5` |
| 47 | (4.4) `Σ 2^j 3^{n−j} = 3ⁿ − 2ⁿ` | the sum is `3(3ⁿ − 2ⁿ)` | `eq4_4_printed_false`; `eq4_4` (exponent `n−1−j`) |
| 48 | proof of Thm 4.1: "at most `m` choices", `F ≤ m·2^{n−m}` | `m + 1` weights; the bound fails for `n = 1`, `M = 2` | `thm4_1_printed_step_false`; `thm4_1_core` with `m + 1`; the final bound holds (`thm4_1`) |

## Prior work

- Theorem 2.1 is, in Lagarias's words, "essentially due to Böhm and Sontacchi". Their paper is formalised in Lean
  ([tcosmo/BohmSontacchi1978_lean](https://github.com/tcosmo/BohmSontacchi1978_lean), ccchallenge status `audited`):
  its Proposition 5 is the integer version (a nonzero integer is a cycle point iff it is `sum/(2ⁿ − 3^m)` for a
  valid schedule). The rational version for every parity word (Lemma 2 of Halbeisen–Hungerbühler 1997, who
  attribute it to Lagarias) is in this repository's `hh1997/`; `thm2_1` adds the uniqueness and the parity word.
- Belaga–Mignotte, *Experimental Math.* 7 (1998) 145–151: Lemma 3.5(2) (injectivity, "observed in [Lagarias 1990]"),
  Proposition 3.6 ("generalizes Böhm–Sontacchi and Lagarias 1990, Theorem 2.1"), Proposition 3.7 and Remark 3.13
  are close to `cor2_1a`, `thm2_1`/`bij3`, the irreducible words, and the construction in `thm3_4`.
- To our knowledge there is no earlier formalisation of Lagarias 1990 (ccchallenge entry `Lagarias1990`:
  not started on 2026-10-20).

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
statement T★, never used (the axiom report of every theorem here excludes `sorryAx`).
