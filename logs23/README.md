# logs23 — a lower bound for |b₁ log 2 − b₂ log 3|, and Steiner 1978 without `H_Rhin`

**Status (2026-10-28): on GitHub (branch `main`), not released** (no release, tag or DOI covers this folder yet).
Lean 4.34.0, Mathlib v4.34.0.

`../steiner1978/` proves Steiner's theorem on circuits (the only circuit on the positive integers that is a cycle
is {1, 2}) under the named hypothesis `H_Rhin` (the case `u₀ = 0` of inequality (7) of G. Rhin, *Approximants de
Padé et mesures effectives d'irrationalité*, Progress in Math. 71 (1987), 155–164), and without hypothesis for
`k ≤ 20000`. That proof uses `H_Rhin` through a single lemma, `rhin_k_le`, to bound `k`. What it needs is much
weaker than `H_Rhin`: for `Λ = (k + l) log 2 − k log 3`,

> `lam_lower`: for every `k > 20000` and every `l ≥ 0`, `1/(2^k − 1) ≤ |Λ|`.

(For `k > 20000`: if `|Λ| < 1` then `k + l < 2k`, and `H_Rhin` gives `|Λ| ≥ (2k)^(−13.3)`, far above `1/(2^k − 1)`.)

This folder proves `lam_lower`, hence Steiner's theorem, **without any hypothesis**. It does not formalise Rhin's
paper and does not prove `H_Rhin` (its lower bound for `|Λ|` is much weaker than Rhin's, but sufficient here).

## What is proved (no hypothesis; axioms `propext`, `Classical.choice`, `Quot.sound` only)

Frozen statements: `Logs23/Logs23_Enonces.lean` (frozen at step 2a, commit 3a127e3) and `Logs23/TwoLog_Enonces.lean`
(frozen at step 2b, commit 7fb3a6f), each written and committed before its proofs. Since then only the header
comment of `Logs23_Enonces.lean` was edited (commits 438f048 and de13596; from this folder,
`git -C .. diff 3a127e3 HEAD -- logs23/Logs23/Logs23_Enonces.lean` shows comment lines only); `TwoLog_Enonces.lean`
is unchanged. Its header
mentions the lab's register; the section "How it is proved" below replaces it.

| statement | content |
|---|---|
| `bridge_gap` | for `0 < k < qBr'` and every integer `L`: `\|pBr log 2 − qBr log 3\| ≤ \|L log 2 − k log 3\|` |
| `bridge_value` | `10^(−101) ≤ \|pBr log 2 − qBr log 3\|` |
| `lam_lower_bridge` | `lam_lower` for `20000 < k < qBr'` |
| `steiner_bridge`, `steiner_cycle_bridge` | Steiner's theorem (Davison's equation; circuits) for `k < qBr'` |
| `two_log_lower` | for every natural `b₁` and every natural `b₂ ≥ 2^334`: `exp(−10^12 ν^5) ≤ \|b₁ log 2 − b₂ log 3\|`, `ν = ⌊log₂ b₂⌋ + 1` |
| `lam_lower_large` | `lam_lower` for `k ≥ 2^334` |
| `lam_lower` | for every `k > 20000` and every `l`: `1/(2^k − 1) ≤ \|Λ\|` |
| `reduction` | `lam_lower` implies the five statements below |
| `steiner_nh`, `steiner_int_nh`, `steiner_cycle_nh`, `steiner_cycle_int_nh`, `tstar_circuit_nh` | the statements `steiner`, `steiner_int`, `steiner_cycle`, `steiner_cycle_int`, `tstar_circuit` of `../steiner1978/` without their premise `H_Rhin` |

Here `pBr/qBr` and `pBr'/qBr'` are two consecutive convergents of `log₂ 3`; `qBr` is the first convergent denominator
with 100 digits and `qBr' ≈ 6.34 · 10^100 > 2^334`.

In particular (`steiner_cycle_nh`): **every circuit on the positive integers that is a cycle is {1, 2}** (it starts
at `n = 1`, with `k = l = 1`), and (`steiner_cycle_int_nh`) every circuit-cycle on `ℤ` is `{−1}`, `{1, 2}` or
`{−5, −7, −10}` (it starts at `n = −1` with `l = 0`, at `n = 1`, or at `n = −5`), with no hypothesis. (These
statements exclude every other circuit-cycle; that the listed ones are circuit-cycles is a direct computation,
not stated in Lean.)
The sixth statement of `../steiner1978/` with the premise `H_Rhin`, `rhin_k_le` ("`k ≤ 108`"), is not stated here
without its premise; it would follow at once from `steiner_int_nh` (a solution with `k ≥ 1`, `l ≥ 1`, `h ≠ 0` has
`k ≤ 2`).

## How it is proved

**Step 2a, the bridge (`k < qBr'`).**
* `Logs23/Encadrements.lean`: `log 2 = 2 artanh(1/3)` and `log(3/2) = 2 artanh(1/5)`; Mathlib's
  `Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add` give rational enclosures of width below
  `10^(−211)` (221 and 155 terms), computed by the kernel (`decide +kernel`).
* `Logs23/Pont.lean`: the basis `(pBr, qBr), (pBr', qBr')` of `ℤ²` is unimodular; write
  `(L, k) = a (pBr, qBr) + b (pBr', qBr')`. For `0 < k < qBr'`, `a ≠ 0` and `a b ≤ 0`; since
  `pBr log 2 − qBr log 3 < 0 < pBr' log 2 − qBr' log 3` (from the enclosures), `|L log 2 − k log 3| ≥ |pBr log 2 − qBr log 3|`.
  This best-approximation argument is classical (convergents are best approximations); it plays the role of the
  numerical computation of partial quotients in Steiner's proof as summarised by J. Simons and B. de Weger,
  *Theoretical and computational bounds for m-cycles of the 3n+1 problem*, Acta Arith. 117 (2005), version 1.44
  (2010), §1.4. No novelty is claimed.
* `Logs23/Principal.lean`: the proofs of `../steiner1978/Steiner/Principal.lean`, with `rhin_k_le_thm` replaced by
  `k_le_of_lam`, which combines a lower bound for `|Λ|` with `lam_small` (a solution with `k ≥ 1`, `l ≥ 1`, `h ≠ 0`
  has `|Λ| < 1/(2^k − 1)`, for either sign of `h`).

**Step 2b, `two_log_lower` (`b₂ ≥ 2^334`).** An interpolation determinant in the spirit of M. Laurent (*Linear forms
in two logarithms and interpolation determinants*, Acta Arith. 66 (1994), 181–199), with crude explicit constants,
for `Λ = b₁ log 2 − b₂ log 3`. Parameters: `L = ν`, `K + 1 = 2^15 ν`, `N = L (K + 1)`, columns `(r, s)`,
`1 ≤ r ≤ 2^8 ν`, `0 ≤ s < S = 2^7 ν`; `ζ_max = 2^9 ν`, `λ_max = ν log 2`.
* `Logs23/Interpolation.lean`: the integer matrix `M[(l,κ),(r,s)] = (r b₂ + s b₁)^κ (2^r 3^s)^(l+1)` satisfies
  `det M = b₂^σ G(δ)`, `G(t) = det[ζ^κ e^{λ_l ζ} e^{(l+1) s t}]`, `ζ = r + s b₁/b₂`, `λ_l = (l+1) log 2`, `δ = −Λ/b₂`,
  `σ = Σ κ` (`det_Mint`); for `N × N` matrices with entries bounded by `M` and entrywise differences bounded by `D`:
  `|det A| ≤ N! M^N`, `|det A − det B| ≤ N · N! · M^(N−1) · D`.
* Instead of a zero lemma, a positivity argument: `Logs23/CauchyBinet.lean` (the Cauchy–Binet formula, not in
  Mathlib v4.34), `Logs23/GenVandermonde.lean` (generalized Vandermonde determinants with increasing positive nodes
  and increasing exponents are positive, by Descartes' rule of signs, Mathlib
  `Polynomial.roots_countP_pos_le_signVariations`), `Logs23/ExpKernel.lean` (all Cauchy–Binet terms of
  `E(x) := det[e^{μ_i x ζ_j}]` have the same sign for distinct positive `μ_i`, `ζ_j` and `x ≥ 0`, hence a lower bound by one
  term and the bound `|E(1)| ≤ x^(−N(N−1)/2) |E(x)|` for `x ≥ 1`), `Logs23/Confluence.lean` (with `μ = λ_l + κ h`, a
  triangular change of rows gives
  `E = h^σ det[…]`, and `h → 0` gives analogous bounds for `D(x) = det[(xζ)^κ e^{λ_l x ζ}]`, `D(1) = G(0)`:
  `|D(1)| ≥ T' := (∏_{m<N} 1/m!) ((log 2)/2)^(N(N−1)/2) |V(ζ)|` and `|D(1)| ≤ x^(−N(N−1)/2) |D(x)|` for `x ≥ 1`).
* `Logs23/Proposition.lean` (`prop_main`): for distinct points (the integers `r b₂ + s b₁` distinct), with
  `X(x) := (x ζ_max)^K e^{λ_max x ζ_max}` bounding the entries and `L S |Λ|/b₂ ≤ 1`: if, for some `x ≥ 1`,
  `N! X(x)^N / x^(N(N−1)/2) ≤ 1/(2 b₂^σ)`, then `|G(0)|` is small; if
  `det M ≠ 0` then `|G(δ)| ≥ b₂^(−σ)`, and if `det M = 0` then `G(δ) = 0`; in both cases
  `|G(δ) − G(0)| ≥ |G(0)| ≥ T' > 0`, and the perturbation bound gives `|Λ| ≥ b₂ T' / (N · N! · (3 X(1))^N · L S)`.
  The case `det M = 0` is not excluded.
* `Logs23/Constantes.lean`: the condition of `prop_main` (with `x = 16`) and the final inequality, for every `ν ≥ 335`
  (logarithms, `log ν ≤ ν/50 + 3`, `n! ≤ n^n`, polynomial inequalities).
* `Logs23/TwoLog.lean`: the grid of points (distinct for coprime `b₁, b₂` with `S ≤ b₂`), the reduction to coprime `b₁, b₂`
  (dividing by the gcd; small reduced denominators are handled by the bridge), then `lam_lower_large`, `lam_lower`
  and the five statements `…_nh` through `reduction`.

We have not checked whether this replacement of the zero lemma by total positivity appears in the literature; it
may well be known. Much stronger explicit bounds are published (Laurent 1994; M. Laurent, M. Mignotte,
Y. Nesterenko, J. Number Theory 55 (1995); N. Gouillon, *Explicit lower bounds for linear forms in two logarithms*,
J. Théor. Nombres Bordeaux 18 (2006), 125–146); the bound here is deliberately crude, because the bridge covers every
`k < qBr'`. Steiner's own proof uses Baker's theorem on linear forms in two logarithms (Lemma 1 of his paper, from
A. Baker, *Transcendental Number Theory*, p. 45; Simons–de Weger, §1.4; see `../steiner1978/README.md`).

The four integers of the bridge were computed by `checks/cf_log23.py` (mpmath, 600 digits; output in
`checks/cf_log23.out.txt`); Lean re-certifies everything it uses about them.

## Re-checking

Prerequisites: git, curl, python3, [elan](https://github.com/leanprover/elan) (the `lean-toolchain` files of this
folder and of `../steiner1978` select Lean 4.34.0), network access (elan downloads Lean 4.34.0, Lake clones Mathlib
and its dependencies, `lake exe cache get` downloads Mathlib's prebuilt files) and disk space: about 8 GB for the
clone (Mathlib's sources and prebuilt files included), plus the Lean 4.34.0 toolchain installed by elan (2.7 GB on
the machine used) and Mathlib's download cache (`~/.cache/mathlib`). From the root of a fresh clone of the
repository:

```bash
cd steiner1978
lake exe cache get
cd ../logs23
./check.sh
```

`./check.sh` checks `SHA256SUMS` (the Lean sources of `Logs23/`), runs `../steiner1978/check.sh` (which builds the
Steiner 1978 modules imported here), compiles `Logs23/*.lean` one by one with `lean -o` (`LEAN_PATH` from `env.sh`:
this folder's build directory, then the `LEAN_PATH` of `../steiner1978`; this folder has no Lake package of its own
and `lake build` is not used), fails on any error or `sorry` warning, and reads the axiom report of
`Logs23/Axiomes.lean`: it fails unless the reports are exactly those of the 15 theorems listed in `check.sh` (the 14
frozen statements and `widths`), each with standard axioms only. Warnings "exponent … exceeds the threshold 256" and
deprecation warnings in the logs are expected. Recorded report: `axioms/Logs23_Axiomes.txt`.

These commands were run on 2026-10-28 from a fresh clone of commit f9c33aa (the later commits change README files
only), on a machine where Lean 4.34.0 was already installed and Mathlib's prebuilt files were already in the local
cache: `../steiner1978/check.sh` read its 12 axiom reports and `./check.sh` its 15, all with standard axioms only;
compared afterwards, they were the same as the recorded ones (`../steiner1978/axioms/Steiner_Axiomes.txt`,
`axioms/Logs23_Axiomes.txt`).

## Credits

Definitions and the finite check `k ≤ 20000` (both signs): `../steiner1978/`. Series bounds for the logarithm,
Descartes' rule of signs, Vandermonde determinants, `Matrix.det_le`: Mathlib. Formalisation written with Claude
(Anthropic), LABO-COLLATZ, directed by Eric Merle.
