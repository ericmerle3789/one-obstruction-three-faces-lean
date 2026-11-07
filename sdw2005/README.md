# sdw2005 — the upper bound for `K` of Simons–de Weger without Rhin's lower bound (m ≤ 82)

**Status: not in a release.** Lean 4.34.0, Mathlib v4.34.0; uses the build of `../steiner1978/` and the modules of
`../logs23/`.

J. Simons and B. de Weger, *Theoretical and computational bounds for m-cycles of the 3n + 1 problem*, Acta Arith.
117 (2005) (version 1.44 of 2010 read; the lemma and theorem numbers below are those of that version), bound the number
`K` of odd steps of an m-cycle from above. Their a priori bound (their Lemmas 12 and 14) uses G. Rhin's lower bound
for `|x log 2 + y log 3|` (Rhin 1987). This folder proves an upper bound for `K` when `m ≤ 82` with the lower bounds
of `../logs23/` instead, so with no hypothesis at all:

> `cycle_K_lt`: if `C^[N] n = n` with `n > 0` and `N > 0`, where `C(n) = n/2` (`n` even) and `(3n + 1)/2` (`n` odd),
> and if at most `82` of the `N` terms `C^[j] n` (`j < N`) are local minima (odd, with an even predecessor in the
> cycle), then fewer than `4·10^18` of these `N` terms are odd.

This is not new mathematics, and it does not prove the Collatz conjecture or exclude any cycle. That any explicit
lower bound for `|x log 2 + y log 3|` gives an a priori bound is in the logic of Simons–de Weger's argument. The bound
`4·10^18` is weaker than theirs: for `78 ≤ m ≤ 90`, Theorem 3(c) of their version 1.44 gives `K < 1.3993·m·δ^m`
(`δ = log₂ 3`), about `2.9·10^18` at `m = 82`; for smaller `m` the same theorem gives more. Their results use a
lower bound `X0` for the elements of a cycle (from computations); `cycle_K_lt` uses none.

## Why `4·10^18` and `m ≤ 82`

C. Hercher, *There are no Collatz m-cycles with m ≤ 91* (J. Integer Seq. 26 (2023), art. 23.3.5; arXiv:2201.00406), uses the
upper bound of Simons–de Weger for `K` (`K < 1.4784·m·δ^m < 2.2·10^20` for `m ≤ 91`). In the Lean formalisation of
Hercher's argument for `m ≤ 82` by P. Norfleet (GitHub `PhilNorfleet/Hercher2023_lean`, read on 2026-11-07), that
bound is a hypothesis, `hSdW : K < 1.4784·m·δ^m`, used to obtain `K < 4·10^18`. `cycle_K_lt` does **not** imply
`hSdW` (for small `m`, `1.4784·m·δ^m` is far below `4·10^18`); it states the bound `K < 4·10^18` itself without
hypothesis, **for the definitions of this folder** (`minCount`, `oddCount`). It could replace the step where `hSdW` is
used only after a bridge lemma between those definitions and the ones of that formalisation (there, `K` counts the
distinct odd values over one period and `m` is the period of the map from a local minimum to the next), and a
restatement of its theorem. Nothing of that repository is copied here.

## What is proved (no hypothesis; axioms `propext`, `Classical.choice`, `Quot.sound` only)

Frozen statements: `Sdw2005/Sdw_Enonces.lean`, committed alone before the proofs (commit 750c7f2) and unchanged
since (SHA-256 in `SHA256SUMS`).

| statement | content |
|---|---|
| `ChainSol m k l a` | the chain equation of Simons–de Weger (§2.1) with `m ≥ 1` blocks, indices modulo `m`: `3^{k_i} a_i − 1 = 2^{k_{i+1} + l_i} a_{i+1} − 2^{l_i}`, all `k_i, l_i, a_i ≥ 1` (a definition) |
| `lemma4` | `0 < Λ < Σ 1/x_i`, where `Λ = (K + L) log 2 − K log 3`, `K = Σ k_i`, `L = Σ l_i`, `x_i = 2^{k_i} a_i − 1` (their Lemma 4) |
| `lemma6` | `x_{i+1} < (x_i + 1)^δ / 2` (the inequality from which their Lemma 6 follows, without `X0`) |
| `lemma7_min` | `x_i ≥ 2^{(δ−1)K/(δ^m−1) − 1}` for every `i` (the lower bound for `x_i` in the proof of their Lemma 7, with `X0 = 1`) |
| `lemma7` | `Λ < 2m · 2^{−(δ−1)K/(δ^m−1)}` (their Lemma 7 with `X0 = 1`, where their constant `c_m` equals `2`) |
| `chain_K_lt` | for every solution of the chain equation with `m ≤ 82`: `K < 4·10^18` |
| `cycle_chain` | a cycle of `C` on the positive integers gives a solution of the chain equation with `m = minCount n N` and `K = oddCount n N` |
| `cycle_K_lt` | the statement quoted above |

## How it is proved

- **Lemma 7 with `X0 = 1`.** With `w_j = log(2 x_j)`, Lemma 6 and `x + 1 ≤ 2x` give `w_{j+1} ≤ δ w_j`, so
  `w_j ≤ δ^j w_0` along the cycle; summing and using `2 x_i ≥ 2^{k_i}` gives `w_0 ≥ (δ−1) K log 2/(δ^m − 1)` for
  every starting index. No lower bound `X0` for the elements of the cycle is used.
- **`chain_K_lt`.** For `m ≤ 82`, `(δ−1)/(δ^m − 1) ≥ 1/(5·10^16)` (`58/100 ≤ δ − 1`, `δ ≤ 317/200`), so
  `Λ < 164 · 2^{−K/(5·10^16)}`. If `K ≥ 4·10^18`: for `K < q₃₉`, best approximation by the convergents `p₃₈/q₃₈` and
  `p₃₉/q₃₉` of `log₂ 3` (`Logs23.gap_of_unimodular`) gives `Λ ≥ 10^(−20) > 164 · 2^(−80)`; for `q₃₉ ≤ K < qBr'`, the
  bridge of `../logs23/` gives `Λ ≥ 10^(−101) > 164 · 2^(−500)`; for `K ≥ qBr' ≥ 2^334`, `Logs23.two_log_lower_thm`
  gives `Λ ≥ exp(−10^12 ν^5)` with `2^(ν−1) ≤ K`, against `Λ < 164 · 2^{−K/(5·10^16)}`. The convergents are indexed
  from `p₀/q₀ = 1/1`; `p₃₉ q₃₈ − p₃₈ q₃₉ = 1` and the signs and sizes of `p log 2 − q log 3` are checked by the kernel
  against the rational enclosures of `log 2` and `log (3/2)` of `../logs23/Logs23/Encadrements.lean`.
- **`cycle_chain`.** The local minima of the orbit `y_j = C^[j] n` are listed by `Nat.nth`; between two consecutive
  minima the orbit has a run of `k_i ≥ 1` odd values (on which `2^j (y_{t+j} + 1) = 3^j (y_t + 1)`) and then a run of
  `l_i ≥ 1` even values; with `a_i = (y_{t_i} + 1)/2^{k_i}` this is the chain equation, the `m`-th minimum is the
  first one plus `N`, and the odd values are counted block by block.

| file | content |
|---|---|
| `Sdw2005/Sdw_Enonces.lean` | the frozen statements |
| `Sdw2005/Chaine.lean` | Lemmas 4, 6, 7 |
| `Sdw2005/Bornes.lean` | the convergents 38 and 39, the bounds on `δ`, `chain_K_lt` |
| `Sdw2005/Cycles.lean` | `cycle_chain`, `cycle_K_lt` |
| `Sdw2005/Axiomes.lean` | statement check (`example`s) and `#print axioms` |

## Re-check

Once, in `../steiner1978/`: `lake exe cache get`. Then `./check.sh` (needs python3). It checks the sources against
`SHA256SUMS`, runs `../logs23/check.sh` (which runs `../steiner1978/check.sh`), compiles each file of `Sdw2005/` with
`lean -o` in dependency order (failing on any error or `sorry`), and reads the `#print axioms` report of
`Sdw2005/Axiomes.lean`: it fails unless the 7 theorems are exactly those expected and depend only on `propext`,
`Classical.choice`, `Quot.sound`. Deprecation warnings and a warning on an exponent above 256 are expected.
