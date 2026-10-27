# logs23 — a lower bound for |L log 2 − k log 3|, towards Steiner 1978 without `H_Rhin`

**Status: work in progress, local only, not released.** Lean 4.34.0, Mathlib v4.34.0.

`../steiner1978/` proves Steiner's theorem on circuits (the only circuit on the positive integers that is a cycle
is {1, 2}) under the named hypothesis `H_Rhin` (the case `u₀ = 0` of inequality (7) of G. Rhin, *Approximants de
Padé et mesures effectives d'irrationalité*, Progress in Math. 71 (1987), 155–164), and without hypothesis for
`k ≤ 20000`. That proof uses `H_Rhin` once, to bound `k`. What it needs is much weaker than `H_Rhin`: for
`Λ = (k + l) log 2 − k log 3`,

> `lam_lower`: for every `k > 20000` and every `l`, `1/(2^k − 1) ≤ |Λ|`.

This folder works towards `lam_lower`. **It does not formalise Rhin's paper and does not prove `H_Rhin`.**

## What is proved (no hypothesis; axioms `propext`, `Classical.choice`, `Quot.sound` only)

| statement (`Logs23/Logs23_Enonces.lean`) | content |
|---|---|
| `bridge_gap` | for `0 < k < qBr'` and every integer `L`: `\|pBr log 2 − qBr log 3\| ≤ \|L log 2 − k log 3\|` |
| `bridge_value` | `10^(−101) ≤ \|pBr log 2 − qBr log 3\|` |
| `lam_lower_bridge` | `lam_lower` for `20000 < k < qBr'` |
| `steiner_bridge`, `steiner_cycle_bridge` | Steiner's theorem (Davison's equation; circuits) for `k < qBr'` |
| `reduction` | `lam_lower` implies `steiner_nh`, `steiner_int_nh`, `steiner_cycle_nh`, `steiner_cycle_int_nh`, `tstar_circuit_nh`: the statements `steiner`, `steiner_int`, `steiner_cycle`, `steiner_cycle_int`, `tstar_circuit` of `../steiner1978/` without their premise `H_Rhin` (the sixth statement there with this premise, `rhin_k_le`, "`k ≤ 108`", is not covered) |

Here `pBr/qBr` and `pBr'/qBr'` are two consecutive convergents of `log₂ 3`; `qBr` is the first denominator with
100 digits and `qBr' ≈ 6.34 · 10^100`. So Steiner's theorem is proved without hypothesis for every circuit with
fewer than `qBr'` odd steps (instead of 20 000 in `../steiner1978/`).

## What is not proved

`lam_lower` for `k ≥ qBr'`. Hence the five statements `…_nh` (Steiner's theorem for all `k`, without `H_Rhin`)
are **not** proved yet. This needs an effective lower bound for linear forms in two logarithms (for instance of
the type of M. Laurent, *Linear forms in two logarithms and interpolation determinants*, Acta Arith. 66 (1994),
181–199, or N. Gouillon, *Explicit lower bounds for linear forms in two logarithms*, J. Théor. Nombres Bordeaux 18
(2006), 125–146); thanks to the bridge, any such bound for `b ≥ 10^100`, whatever its constants, would suffice.
None is formalised here.

## How the bridge is proved

* `Logs23/Encadrements.lean`: `log 2 = 2 artanh(1/3)` and `log(3/2) = 2 artanh(1/5)`; Mathlib's
  `Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add` give rational enclosures of width below
  `10^(−211)` (221 and 155 terms), computed by the kernel (`decide +kernel`).
* `Logs23/Pont.lean`: the basis `(pBr, qBr), (pBr', qBr')` of `ℤ²` is unimodular (`pBr' qBr − pBr qBr' = 1`); write
  `(L, k) = a (pBr, qBr) + b (pBr', qBr')`. For `0 < k < qBr'`, `a ≠ 0` and `a b ≤ 0`; since
  `pBr log 2 − qBr log 3 < 0 < pBr' log 2 − qBr' log 3` (from the enclosures), `|L log 2 − k log 3| ≥ |pBr log 2 − qBr log 3|`.
  No continued-fraction theory is used in Lean: only the two pairs of integers and two certified signs.
  This best-approximation argument is classical; no novelty is claimed.
* `Logs23/Principal.lean`: the proofs of `../steiner1978/Steiner/Principal.lean`, with `rhin_k_le_thm` replaced by
  `k_le_of_lam` (a solution with `l ≥ 1`, `h ≠ 0` has `|Λ| < 1/(2^k − 1)`, for either sign of `h`).

The four integers were computed by `checks/cf_log23.py` (mpmath, 600 digits; output in `checks/cf_log23.out.txt`);
Lean re-certifies everything it uses about them.

## Re-checking

`./check.sh`: checks `SHA256SUMS`, runs `../steiner1978/check.sh` (which builds the Steiner 1978 modules imported
here), compiles `Logs23/*.lean` one by one with `lean -o` (`LEAN_PATH` from `env.sh`), and reads the axiom report
of `Logs23/Axiomes.lean` (expected: 6 reports, standard axioms only). Prerequisite: Mathlib's prebuilt cache
(`lake exe cache get` in `../steiner1978`). Recorded report: `axioms/Logs23_Axiomes.txt`.

## Credits

Definitions and the finite check `k ≤ 20000` (both signs): `../steiner1978/`. Series bounds for the logarithm:
Mathlib. Formalisation written with Claude (Anthropic), LABO-COLLATZ, directed by Eric Merle.
