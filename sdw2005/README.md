# sdw2005 — an upper bound for `K` in the way of Simons–de Weger, without Rhin's lower bound (m ≤ 82, m ≤ 91)

**Status: in this repository since release v1.8** (its first release that contains this folder), archived on Zenodo;
concept DOI [10.5281/zenodo.23498095](https://doi.org/10.5281/zenodo.23498095), which resolves to the latest version;
the DOI of v1.8 is 10.5281/zenodo.24049927. Lean 4.34.0, Mathlib v4.34.0; uses the build of `../steiner1978/` and
the modules of `../logs23/`.
*(2026-11-08.)* `Sdw2005/Pont_Enonces.lean` and `Sdw2005/Pont.lean` (the same bounds counted on distinct values, below)
were added after release v1.8; they are in release v1.9.

J. Simons and B. de Weger, *Theoretical and computational bounds for m-cycles of the 3n + 1 problem*, Acta Arith.
117 (2005) (version 1.44 of 2010 read; the lemma and theorem numbers below are those of that version), bound the number
`K` of odd steps of an m-cycle from above. Their a priori bound (their Lemmas 12 and 14) uses G. Rhin's lower bound
for `|x log 2 + y log 3|` (Rhin 1987). This folder proves upper bounds for `K` when `m ≤ 82` and when `m ≤ 91` with
the lower bounds of `../logs23/` instead, so with no hypothesis at all:

> `cycle_K_lt`: if `C^[N] n = n` with `n > 0` and `N > 0`, where `C(n) = n/2` (`n` even) and `(3n + 1)/2` (`n` odd),
> and if at most `82` of the `N` terms `C^[j] n` (`j < N`) are local minima (odd, with an even predecessor in the
> cycle), then fewer than `4·10^18` of these `N` terms are odd.
>
> `cycle_K_lt_91`: the same with at most `91` local minima instead of `82`, and fewer than `2·10^21` odd terms.

This is not new mathematics, and it does not prove the Collatz conjecture or exclude any cycle. That any explicit
lower bound for `|x log 2 + y log 3|` that decays more slowly than exponentially in `K` (Rhin's, or those of
`../logs23/`) gives an a priori bound is in the logic of Simons–de Weger's argument.

Compared with their bounds: their initial bound `K < K1(m)` (Lemma 14, §6.1) is the one that uses Rhin's lower bound;
solving the equation that defines `K1(m)` (our computation, which gives back their table values at `m = 64` and
`m = 100`) gives `K1(82) ≈ 3.8·10^19` and `K1(91) ≈ 2.6·10^21`. `K1(m)` grows with `m`: as a bound for all `m ≤ 82`
(resp. `m ≤ 91`), `4·10^18` (resp. `2·10^21`) is below `K1(82)` (resp. `K1(91)`), but `K1(m)` is already below
`4·10^18` for `m ≤ 77` and below `2·10^21` for `m ≤ 90`. In this range of `K`, the lower bounds for `Λ` used here,
from continued fractions of `log₂ 3` (the bridge of `../logs23/`, and the convergents 38 and 39 for `m ≤ 82`), are
stronger than Rhin's; their later steps also use continued fractions. Both bounds for `K` are weaker than their final
bounds (Lemma 16 in §6.2, and §7, which rests on Lemma 16; both rest on `K < K1(m)`), stated in Theorem 3(d) of
their version 1.44: for `78 ≤ m ≤ 90`, `K < 1.3993·m·δ^m` (`δ = log₂ 3`), about `2.9·10^18` at `m = 82`, and for
`91 ≤ m ≤ 515 619`, `K < 1.4784·m·δ^m`, below `2.2·10^20` at `m = 91` (about ten times smaller than `2·10^21`); for
smaller `m`, parts (b) and (c) of that theorem give more. Their results use a lower bound `X0` for the elements of a
cycle (from computations); `cycle_K_lt` and `cycle_K_lt_91` use none.

## Why `4·10^18` with `m ≤ 82`, and `2·10^21` with `m ≤ 91`

C. Hercher, *There are no Collatz m-cycles with m ≤ 91* (J. Integer Seq. 26 (2023), art. 23.3.5; arXiv:2201.00406), uses the
upper bound of Simons–de Weger for `K` (`K < 1.4784·m·δ^m < 2.2·10^20` for `m ≤ 91`, as he quotes it; their
Theorem 3 states it for `91 ≤ m ≤ 515 619` in part (d) and implies it for `m ≤ 90` through parts (b)–(d)). In the
Lean formalisation of Hercher's argument for `m ≤ 82` by P. Norfleet (GitHub `PhilNorfleet/Hercher2023_lean`, read on 2026-11-07), that
bound is a hypothesis, `hSdW : K < 1.4784·m·δ^m`, used to obtain `K < 4·10^18`. `cycle_K_lt` does **not** imply
`hSdW` (for small `m`, `1.4784·m·δ^m` is far below `4·10^18`); it states the bound `K < 4·10^18` itself without
hypothesis, **for the definitions of this folder** (`minCount`, `oddCount`). It could replace the step where `hSdW` is
used only after a bridge lemma between those definitions and the ones of that formalisation (there, `K` counts the
distinct odd values over one period and `m` is the period of the map from a local minimum to the next), and a
restatement of its theorem. Nothing of that repository is copied here.
*(2026-11-08.)* The part of that bridge that depends only on this folder is now proved: see *Counting distinct values*
below. In that formalisation (same map `C`), `K` is the number of distinct odd values among `C^[j] n1`, `j < N`, for
`N = blockStart n1 m`, which is `(oddValues n1 N).card` here; so `pont_image` gives `K < 4·10^18` there once it is
shown, with that formalisation's definitions, that `C^[N] n1 = n1` and that these `N` terms contain at most `82` local
minima in the sense of `minCount` (odd, with an even cyclic predecessor). That last step is not done here.

For `m ≤ 91`, the proof of the main theorem in the arXiv version read (v3, 2023-04-04) iterates lower bounds for
`K` (with a lower bound `X0` for the elements of a cycle, from computations) up to `K > 7.94·10^21`, and uses the upper bound
`2.2·10^20` above only in its last comparison. The bound `2·10^21` of `cycle_K_lt_91` is also below `7.94·10^21`, as
is, by our computation above, the initial bound `K1(91) ≈ 2.6·10^21` of Simons–de Weger. But that iteration uses
Hercher's Theorem 21, and P. Norfleet's repository (`SUMMARY.md`, read on 2026-11-07) reports an error near the end of
its proof: with a bound that it could prove instead, the iteration stops near `K ≈ 4.6·10^18`, which is enough only
for `m ≤ 82`; according to the same file, the zbMATH review of the paper (Zbl 1536.11052, not read here) also mentions
a possible flaw near the end of that proof. We have not checked this. So `K > 7.94·10^21` may not be established, and
`cycle_K_lt_91` is offered as a statement on its own.
*(Added 2026-11-08, later the same day.)* The journal version of the paper (J. Integer Seq. 26 (2023), Article 23.3.5)
has a corrigendum by the author, dated 14 June 2026 and linked from the article's page on the journal's site (arXiv is still
at v3 and does not have it). It acknowledges the error at the end of the proof of Theorem 21 (the one also reported in
P. Norfleet's repository) and proves in another way the inequality used afterwards: the window of `m2` consecutive local
minima is chosen with the largest sum of `log₂(n_i + 1)`, so that Lemma 20 bounds the growth by `δ` all around the window,
and a convexity argument gives the bound. We read it and found it correct; one step (the maximum of a convex function is
reached at a vertex) needs one more line, because the set of constraints is not bounded, and that line is easy (the function
decreases along every unbounded direction of that set). We also recomputed the iteration of the proof of Theorem 23 from
the statement of Theorem 21: the same values, up to `K > 7.94·10^21`, and, for each `m` from 83 to 91, a final lower bound
above `1.4784·m·δ^m`. We did not re-check Theorem 14 of the paper, the bounds of Simons–de Weger it uses, or the value of
`X0`. So, as far as we checked, the error is real in the printed proof, the corrigendum repairs it, and `m ≤ 91` stands.
Nothing in this folder changes, and `cycle_K_lt_91` is still offered as a statement on its own.
The statements of the results used along the way (his Theorem 21 and Lemma 22 in that version) contain no upper bound
for `K`, but their proofs were not checked here for that, the starting point `K > 7·10^11` is taken from Theorem 3 of
Simons–de Weger, and the same bridge lemma between definitions would be needed; so this folder does not give a proof
of Hercher's theorem without Rhin's lower bound. The value `2·10^21` is chosen so that the proof needs no pair of
convergents of `log₂ 3` other than the bridge of `../logs23/` (see below).

## Counting distinct values (added 2026-11-08)

`cycle_K_lt` and `cycle_K_lt_91` count terms. Four more statements give the same bounds for the number of distinct
odd values, with `orbitSet n N = {C^[j] n | j < N}` and `oddValues n N` its odd elements (`Sdw2005/Pont_Enonces.lean`):

> `pont_image` (resp. `pont_image_91`): if `C^[N] n = n` with `n > 0`, `N > 0`, and `minCount n N ≤ 82` (resp. `91`),
> then `(oddValues n N).card < 4·10^18` (resp. `2·10^21`). No minimality of `N` is assumed.
>
> `pont_minimal` (resp. `pont_minimal_91`): over the minimal period `N = minimalPeriod C n > 0`, if at most `82`
> (resp. `91`) distinct values of the orbit are local minima (`minValues n N`), then `(oddValues n N).card <
> 4·10^18` (resp. `2·10^21`).

Proof (`Sdw2005/Pont.lean`): distinct odd values are at most odd terms (`Finset.card_image_le`); over the minimal
period, `j ↦ C^[j] n` is injective on `[0, N)` (`Function.iterate_injOn_Iio_minimalPeriod`), so values and terms are
counted alike, for odd values and for local minima. Bookkeeping only; nothing new.

## What is proved (no hypothesis; axioms `propext`, `Classical.choice`, `Quot.sound` only)

Frozen statements: `Sdw2005/Sdw_Enonces.lean`, committed before its proofs with no proof file (commit 750c7f2, with
the set-up files of the folder; its header says "committed alone": it was the only Lean file of that commit), and
`Sdw2005/Sdw91_Enonces.lean`, committed alone before its proofs (commit 21b4ae5); both unchanged since (SHA-256 in
`SHA256SUMS`). *(2026-11-08.)* `Sdw2005/Pont_Enonces.lean` was committed alone before its proofs (commit 972f1e5).

| statement | content |
|---|---|
| `ChainSol m k l a` | the chain equation of Simons–de Weger (§2.1) with `m ≥ 1` blocks, indices modulo `m`: `3^{k_i} a_i − 1 = 2^{k_{i+1} + l_i} a_{i+1} − 2^{l_i}`, all `k_i, l_i, a_i ≥ 1` (a definition) |
| `lemma4` | `0 < Λ < Σ 1/x_i`, where `Λ = (K + L) log 2 − K log 3`, `K = Σ k_i`, `L = Σ l_i`, `x_i = 2^{k_i} a_i − 1` (their Lemma 4) |
| `lemma6` | `x_{i+1} < (x_i + 1)^δ / 2` (the inequality from which their Lemma 6 follows, without `X0`) |
| `lemma7_min` | `x_i ≥ 2^{(δ−1)K/(δ^m−1) − 1}` for every `i` (the lower bound for `x_i` in the proof of their Lemma 7, with `X0 = 1`) |
| `lemma7` | `Λ < 2m · 2^{−(δ−1)K/(δ^m−1)}` (their Lemma 7 with `X0 = 1`, where their constant `c_m` equals `2`) |
| `chain_K_lt` | for every solution of the chain equation with `m ≤ 82`: `K < 4·10^18` |
| `cycle_chain` | a cycle of `C` on the positive integers gives a solution of the chain equation with `m = minCount n N` and `K = oddCount n N` |
| `cycle_K_lt` | the first statement quoted above |
| `chain_K_lt_91` | for every solution of the chain equation with `m ≤ 91`: `K < 2·10^21` |
| `cycle_K_lt_91` | the second statement quoted above |
| `pont_image`, `pont_image_91` | the bounds of `cycle_K_lt`, `cycle_K_lt_91` for distinct odd values (added 2026-11-08) |
| `pont_minimal`, `pont_minimal_91` | the same over the minimal period, with distinct local-minimum values in the hypothesis (added 2026-11-08) |

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
- **`chain_K_lt_91`.** For `m ≤ 91`, `(δ−1)/(δ^m − 1) ≥ 1/(3·10^18)`, so `Λ < 182 · 2^{−K/(3·10^18)}`. If
  `K ≥ 2·10^21`: for `K < qBr'`, the bridge gives `Λ ≥ 10^(−101) > 182 · 2^(−600)`; for `K ≥ qBr'`,
  `Logs23.two_log_lower_thm` as above, with `10^40 ν^5 ≤ 2^(ν−3)` for `ν ≥ 335`. No pair of convergents other than
  the bridge is used.
  `cycle_K_lt_91` follows from `cycle_chain`.
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
| `Sdw2005/Sdw91_Enonces.lean` | the frozen statements for `m ≤ 91` |
| `Sdw2005/Borne91.lean` | `chain_K_lt_91`, `cycle_K_lt_91` |
| `Sdw2005/Pont_Enonces.lean` | the frozen statements on distinct values (added 2026-11-08) |
| `Sdw2005/Pont.lean` | their proofs (added 2026-11-08) |
| `Sdw2005/Axiomes.lean` | statement check (`example`s) and `#print axioms` |

## Re-check

Once, in `../steiner1978/`: `lake exe cache get`. Then `./check.sh` (needs python3). It checks the sources against
`SHA256SUMS`, runs `../logs23/check.sh` (which runs `../steiner1978/check.sh`), compiles each file of `Sdw2005/` with
`lean -o` in dependency order (failing on any error or `sorry`), and reads the `#print axioms` report of
`Sdw2005/Axiomes.lean`: it fails unless the 13 theorems (9 up to release v1.8) are exactly those expected and depend only on `propext`,
`Classical.choice`, `Quot.sound`. Deprecation warnings and a warning on an exponent above 256 are expected.
This folder was re-run from a fresh GitHub clone of commit e2fdb2e (2026-11-07), with Lean 4.34.0 already installed and
Mathlib's download cache already filled: exit 0, 8 minutes including `lake exe cache get` and the runs of
`steiner1978/check.sh` and `logs23/check.sh` that `check.sh` starts, 9 axiom reports, `axioms/Sdw2005_Axiomes.txt`
identical byte for byte to the log of the run.
*(2026-11-08, release v1.9.)* Re-run again, with its 13 axiom reports, as part of the re-run of `../brox2000/` from a
fresh GitHub clone of commit 9077bda (see `../brox2000/README.md`, *Re-check*).
