# Lagarias 1990 in Lean 4

J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arithmetica 56 (1990), 33–53
([PDF, ICM](http://matwbn.icm.edu.pl/ksiazki/aa/aa56/aa5614.pdf), [EuDML 206298](https://eudml.org/doc/206298),
MR 91i:11024).

> **What this is.** A formalisation of a classical paper from 1990. It proves nothing new about Collatz cycles:
> every theorem here is the paper's, sometimes repaired where the printed statement or proof has a slip
> (each repair is listed below, next to what is printed).

**Status (2026-10-20).**
- **Kernel-checked:**
  - Section 2 (Theorem 2.1, Corollaries 2.1a–b and the facts around them, the count (2.4)–(2.5) of irreducible
    cycles);
  - Section 3: the `3x+k` maps, the bijection with rational cycles, Theorems 3.1, 3.2, 3.4 and 3.5;
  - Theorems 4.1 and 4.2 (4.2 with the printed constant `2n⁴`);
  - Tables 2.1, 2.2 and 3.1.
- **Named hypotheses:** Theorem 3.1 with the printed constant uses the prime number theorem, and Theorem 3.2 uses
  Baker–Fel'dman. Both enter as **named hypotheses**, never as axioms. Theorem 3.1 is also proved **without any
  hypothesis**, with the constant 6/5 instead of 5/4.
- **Every frozen statement is proved.**
- **Out of scope:** Theorems 3.3 and 4.3 (see below).

In numbers:
- **59 proved statements.** Each was frozen in a `*_Enonces.lean` file before its proof was written, and each is
  checked by `example : X := X_thm` in `Lagarias/Axiomes.lean`.
- **0 frozen statement left unproved.**
- **0 `sorry`** in the proofs (one unused marker in a copied dependency, see *Dependencies*).
- **0 `native_decide`:** table computations use `decide +kernel`.
- **Axioms:** only `propext`, `Classical.choice`, `Quot.sound` (log in [`axioms/`](axioms/)).
- **Lean 4.34.0, Mathlib v4.34.0**, i.e. after the fix of the kernel soundness bug
  [lean4#14576](https://github.com/leanprover/lean4/issues/14576) (v4.32.2).

## How to check

```bash
cd lagarias1990
lake exe cache get
./check.sh
```

`check.sh` compiles the files one by one with `lake env lean`, in dependency order. It then reads the
`#print axioms` output of `Lagarias/Axiomes.lean`, and fails if any theorem depends on an axiom other than the
three above. It was run from a clean build on 2026-10-20 (21 files, about 4½ minutes on an M1 Pro once Mathlib is cached).

## Named hypotheses

| name | content | source |
|---|---|---|
| `H_PNT` | `θ(x)/x → 1` (Chebyshev's `θ` of Mathlib) | the prime number theorem, which Lagarias uses as `log[1,k] = k + o(k)` (Hardy–Wright Thm 434); it is not in Mathlib v4.34 |
| `H_BF` | `∃ c₁, ∀ n ≥ 2, ∀ l, ½·n^{−c₁}·2ⁿ ≤ |2ⁿ − 3^l|`, i.e. (3.3) | a consequence of the Baker–Fel'dman bound on linear forms in logarithms (Baker 1975, Thm 3.1) |

They appear only as hypotheses of `thm3_1` (`H_PNT → …`) and `thm3_2` (`H_BF → …`).

## Layout

| file | content |
|---|---|
| `Lagarias/L1990_Enonces.lean`, `L1990b_Enonces.lean`, `Tables_Enonces.lean`, `Addenda_Enonces.lean` | frozen statements, each with a line-by-line comparison with the paper in its header |
| `Lagarias/L2_Preuves.lean`, `L3_Preuves.lean`, `L4_Preuves.lean`, `Tables.lean` | phase 2a proofs (Sections 2, 3, 4, tables) |
| `Lagarias/L3b_Preuves.lean`, `L4b_Preuves.lean` | phase 2b proofs (Theorems 3.1–3.2, Ash's bound, Theorem 4.2) |
| `Lagarias/Mots.lean` | primitive words, absent from Mathlib: periods closed under `gcd`, unique irreducible root, free action of the rotations |
| `Lagarias/L2b_Preuves.lean`, `L4c_Preuves.lean` | phase 2c proofs ((2.4), (2.5), Table 2.1; Theorem 4.2 with `2n⁴`) |
| `Lagarias/Addenda.lean` | three points raised by the adversarial review (see below) |
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
| Table 2.2 | `table2_2_values`, `table2_2_complete`, `table2_2_gcd` | proved: the 23 rows, completeness for `n ≤ 6`, the `110000` remark |
| p. 40, clearing denominators; `T_{dk'}(dn') = d·T_{k'}(n')` | `clear_den`, `tk_scale` | proved |
| p. 40, rational cycles ↔ primitive cycles of the `T_k`, `k > 0`, `k ≡ ±1 (6)` | `bij3` | proved (`Set.BijOn`) |
| p. 44, the smallest member of a primitive cycle is `≡ ±1 (6)` (used, not proved in the paper) | `no3`, `min_pm1` | proved for positive cycles; false for negative ones, see below |
| Theorem 3.1 | `thm3_1` (`H_PNT`), `thm3_1_65` | proved: with `5/4` under `H_PNT`; with `6/5` unconditionally (Chebyshev's bound `θ(n) ≥ n log 2 − O(√n log n)` of Mathlib). The proof runs over the primes `p ≥ 5`, so the `k` found are primes |
| proof of Thm 3.1: `k ∣ 2ⁿ − 3^l`; `S(t) ≤ 3^{t(t+1)(2t+1)/6}` | `k_dvd_D`, `S31_bound` | proved |
| Theorem 3.2 | `thm3_2` (`H_BF`) | proved, with `log₂` and `|D(v)|`, from `thm3_1_65` (so without `H_PNT`) |
| Theorem 3.4 | `thm3_4` | proved; the first claim also for even `n0` |
| pp. 44–45, the examples `1/(2^m − 3)` and `5/(2^m − 9)` | `ex_10m`, `ex_5` | proved, with `v` of total length `m` |
| (3.8)–(3.9) | `eq3_8` | proved |
| Theorem 3.5 | `thm3_5` | proved |
| (4.4), (4.5), (4.8) | `eq4_4`, `eq4_5`, `eq4_8` | proved ((4.4) with the exponent repaired) |
| Theorem 4.1 | `thm4_1`, `thm4_1_core`, `thm4_1_printed_step_m1` | proved |
| Ash, Lemma 4.7.2 | `ash_tail` | proved (Chernoff's argument) |
| Theorem 4.2 | `thm4_2_printed`, `thm4_2` | proved with the printed constant `2n⁴`, and with the constant `4n⁴` that the printed proof gives (see below) |
| Table 3.1 | `table3_1_rows`, `table3_1_row35`, `table3_1_row73` | the 48 printed `n0` are in primitive cycles of the printed length (their minimality is confirmed numerically, not in Lean); the 2 other rows are corrected, with minimality in Lean |
| Theorem 3.3, Theorem 4.3, (4.13)–(4.14), Remark (4)/(4.19) | — | **out of scope**: asymptotic results that need Baker's bound and the divisor bound `d(B) ≤ B^{c/log log B}` (Hardy–Wright Thm 317) |
| Fig. 4.1 (the flat segment) | — | out of scope: the paper omits the proof |
| the conjectures (§3.1, Conjecture P, Equidistribution) and the heuristic of §3.5 | — | not theorems |

## What is printed, what is wrong, what is proved

Each row below was handled in three steps:
- read on the page image;
- checked here by the Lean kernel;
- for the numerical ones, recomputed independently in Python.

The list was then read by an adversarial reviewer, whose three corrections are included (marked *review*). As far
as checked, none of these points is reported in print: Lagarias's own annotated bibliography, entry 108, lists no
erratum.

| page | printed | what is wrong | proved here |
|---|---|---|---|
| 37 | proof of Cor. 2.1a: `x(v) = (2ⁿ − 3^k)^{−1} Σ …` | the word has `k+1` ones | `eq1_3` (exponent `k+1`) |
| 39 | "`T` does not change the denominator" | ambiguous (*review*). It is true for the formal denominator `q` of `a/q`; it is false for the reduced one, since `T(1/3) = 1` | `den_formal`, `den_printed_false`; the conclusion `den_cycle` holds |
| 40 | `(D(v), 6) = 1` | `v = 00` gives `D = 3`. Only the reducible word `0ⁿ` (`x = 0`) fails; `k ≡ ±1 (6)` is unaffected | `D6_printed_false`; `D6` (when `v` has a 1) |
| 40 | `T_k(n) = T_{−k}(−n)` | `T_1(1) = 2`, but `T_{−1}(−1) = −2` | `tk_sign_printed_false`; `tk_sign`: `T_k(n) = −T_{−k}(−n)` |
| 40 | `T_k(Z(d,k)) ⊆ Z(d,k)` (`k` odd) | `T_9(1) = 6`, `(6,9) = 3`. Needs `3 ∤ k`, which the next paragraph assumes | `tk_Z_printed_false`; `tk_Z` with `3 ∤ k` |
| 41 | Table 3.1, `k = 35`: `(7, 3)` | `{7, 28, 14}` is not primitive | `table3_1_row35`: `(13, 8)` |
| 41 | Table 3.1, `k = 73`: `(19, 60)` | `5` is in a primitive cycle of length 12 | `table3_1_row73`: `(5, 12)` |
| 41 | "for `n = 85, 107, 139`, `min_l |2ⁿ − 3^l| ≥ ⅓·2ⁿ`" | these are the `k`'s. The periods are `100, 106, 136`, and there the bound fails | `p41` |
| 42 | proof of Thm 3.1: "if all `T_l`, `k0 ≤ l ≤ k`, have a short primitive cycle…" | the range includes `l` with `3 ∣ l`, which have no primitive cycle at all, so the contraposition can only produce such an `l` | `thm3_1`, `thm3_1_65` (argument over primes `p ≥ 5`) |
| 42 | (3.2) `k ≤ (log D(v))³` | the proof gives it with `log₂` and `|D(v)|` | `thm3_2` |
| 43 | proof of Thm 3.3: "at least `n^{−1}C(2n,n)` primitive cycles (with period dividing `n`)" | for every `n` the number is about `C(2n,n)/(2n)`: for `n = 1` there is one cycle, not two. Also "`n`" should be "`2n`" | `thm3_3_count_printed_false` (`n = 1`) |
| 44 | the smallest member of a primitive cycle is "always" `≡ ±1 (6)` | true for positive cycles. False for negative ones if "smallest" is the minimum (*review*): `{−5, −7, −10}` has minimum `−10 ≡ 2` | `min_pm1`; `min_neg_printed_false` |
| 44 | proof of Thm 3.4: `p = ord_{N(v)}(2)` | undefined when `N(v)` is even (`n0` even) | `thm3_4` uses the odd part of `N(v)` |
| 44–45 | `v = 10^m`, `v = 1²0^m` | `v` must have total length `m` | `ex_10m`, `ex_5` |
| 47 | (4.4) `Σ 2^j 3^{n−j} = 3ⁿ − 2ⁿ` | the sum is `3(3ⁿ − 2ⁿ)` | `eq4_4_printed_false`; `eq4_4` (exponent `n−1−j`) |
| 48 | proof of Thm 4.1: "at most `m` choices", `F ≤ m·2^{n−m}` | (*review*) the count is RIGHT for `m ≥ 1`: the head of weight 0 excludes the others. The justification (one head per weight `0…m`) is loose, and the bound fails only for `m = 0`, i.e. `M = 2` | `thm4_1_printed_step_m1`; `thm4_1_printed_step_false` (`M = 2`); the final bound `thm4_1` |
| 48–50 | Thm 4.2: `F ≤ 2n⁴·2^{(1−α)n}` | the statement is right; the printed proof only gives `4n⁴`, because it bounds the normal vectors by `(n−m)·m·2^{n−m}` and then `(n−m)·m ≤ n(n−1)`. That count is itself off by one twice (*review*): `0 ≤ l ≤ n−m` gives `n−m+1` window positions, and the bound per position is printed `(n−m+1)·2^{n−m}` instead of the `m·2^{n−m}` of the claim just before; the Lean count is `(n−m+1)(m+1)·2^{n−m}`. The arithmetic–geometric mean bound `(n−m+1)(m+1) ≤ (n+2)²/4` gives `n²(n+2)² + n ≤ 2n⁴` (for `n ≥ 5`; `n ≤ 4` is trivial), with the paper's own choice of `m` | `thm4_2_printed` (`2n⁴`); `thm4_2` (`4n⁴`, the printed proof) |

Other printed slips, found on reading, that change no Lean statement:
- p. 34: "`k ≡ 1 (mod 6)`" should read `±1`.
- p. 39: "the only row with `D ≠ δ`" holds up to the sign of `D`.
- p. 41: "given by (3.1)" should read (2.1).
- p. 44: `k_m = (2^m − 3^l)/G_0` should read `2^{n+m}`.
- p. 45: "if `x(v) ≤ 0`" should read `< 0`; `a(l)` should read `a(l−1)`.
- p. 47: "`0 ≤ M ≤ n`" should read `0 ≤ l ≤ n`.
- p. 50: "flat segment between `α_c` and 1" should read "between `α_c` and `(log₂ 3)α_c`".
- pp. 35 and 51: `β_c = 1/(1 − α_c) ≐ 1.050005`; the value is `1.050044` (`= 2 − H(φ)`).
- pp. 35 and 52: the intro bound has `(β log k)⁶` while (4.19) has `⁵`.

## Prior work

- **Böhm–Sontacchi.** Lagarias says Theorem 2.1 is "essentially due to Böhm and Sontacchi". Their paper is
  formalised in Lean ([tcosmo/BohmSontacchi1978_lean](https://github.com/tcosmo/BohmSontacchi1978_lean),
  ccchallenge status `audited`). Its Proposition 5 is the integer version: a nonzero integer is a cycle point iff it
  is `sum/(2ⁿ − 3^m)` for a valid schedule.
- **Halbeisen–Hungerbühler 1997.** The rational version for every parity word is their Lemma 2 (they attribute it
  to Lagarias); it is in this repository's `hh1997/`. `thm2_1` adds the uniqueness and the parity word.
- **Belaga–Mignotte**, *Experimental Math.* 7 (1998) 145–151, has close counterparts of several results here:
  - Lemma 3.5(2) (injectivity, "observed in [Lagarias 1990]") ↔ `cor2_1a`;
  - Proposition 3.6 ("generalizes Böhm–Sontacchi and Lagarias 1990, Theorem 2.1") ↔ `thm2_1`, `bij3`;
  - Proposition 3.7 ↔ the irreducible words;
  - Remark 3.13 ↔ the construction in `thm3_4`.
- **Earlier formalisations.** To our knowledge there is none of Lagarias 1990 (ccchallenge entry `Lagarias1990`:
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
statement T★. It is never used; the axiom report of every theorem here excludes `sorryAx`.
