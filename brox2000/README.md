# brox2000 — Brox 2000, *Collatz cycles with few descents*, for the cycles on the positive integers (phase A)

**Status (2026-11-08): on `main`, not in a release.** Lean 4.34.0, Mathlib v4.34.0; uses the build of
`../steiner1978/` and the modules of `../logs23/` and `../sdw2005/`.

T. Brox, *Collatz cycles with few descents*, Acta Arith. 92 (2000), 181–188, DOI
[10.4064/aa-92-2-181-188](https://doi.org/10.4064/aa-92-2-181-188) (read in full on 2026-11-08, from the free copy of
the ICM digital library).

## What Brox proves

Brox works with `T₁(x) = (3x + 1)/2^{k(x)}` on the odd integers, `2^{k(x)} ∥ 3x + 1`. A *Collatz cycle* `Γ` is a cycle
of `T₁` (the odd elements of a cycle of `T(x) = x/2`, `(3x + 1)/2`), `|Γ|` its number of elements, and an element `x`
is *descending* if `k(x) ≥ 2`; `δ(Γ)` is the number of descending elements.

* **Theorem 1.1.** Only finitely many Collatz cycles satisfy `δ(Γ) < 2 log |Γ|` (natural logarithm).
* **Corollary 1.2.** For each `ν ≥ 1`, only finitely many Collatz cycles have `δ(Γ) ≤ ν`.
* **Lemma 2.2** (the part used): the period `k` of the cycle of `T` is at most `2 |Γ|`; so for each `n` only finitely
  many Collatz cycles have `|Γ| = n`.

Steiner's theorem (1978; `../steiner1978/`, `../logs23/`) is the case `δ(Γ) = 1` on the positive integers, with the
exact answer. Brox's theorems cover the cycles on all of `ℤ` (so also the cycles of `T` on the negative integers), and
his Remark 4.1 sketches the extension to `3x + d`.

## What this folder proves

Only the cycles on the **positive** integers (phase A). With `C = Sdw2005.C` (`C n = n/2` for `n` even,
`(3n + 1)/2` for `n` odd), for `n > 0` on a cycle (`Function.minimalPeriod C n > 0`):

* `Gamma n`: the distinct odd values `C^[j] n`, `j < minimalPeriod C n` — Brox's `Γ`;
* `descSet n`: the `x ∈ Gamma n` with `C x` even — Brox's descending elements (for `x` odd, `C x = (3x + 1)/2` is even
  if and only if `4 ∣ 3x + 1`, i.e. `k(x) ≥ 2`).

| statement (`Brox2000/Brox_Enonces.lean`, frozen before the proofs) | content | in the paper |
|---|---|---|
| `lemma22_pos` | `minimalPeriod C n ≤ 2 · \|Gamma n\|` | Lemma 2.2, `k ≤ 2n` |
| `lemma22_finite_pos` | for every `K`, finitely many `n > 0` lie on a cycle with `\|Gamma n\| ≤ K` | Lemma 2.2, second sentence |
| `thm11_pos_explicit` | `\|descSet n\| < 2 log \|Gamma n\|` implies `\|Gamma n\| < 2^1500` | Theorem 1.1, with an explicit bound |
| `thm11_pos` | finitely many `n > 0` lie on a cycle with `\|descSet n\| < 2 log \|Gamma n\|` | **Theorem 1.1** (positive cycles) |
| `cor12_pos` | for every `ν`, finitely many `n > 0` lie on a cycle with `\|descSet n\| ≤ ν` | **Corollary 1.2** (positive cycles) |

All 5 are proved, with no hypothesis, and depend only on the axioms `propext`, `Classical.choice`, `Quot.sound`
(`axioms/Brox2000_Axiomes.txt`). "Finitely many integers on such cycles" and "finitely many such cycles" say the same
thing, since a cycle has finitely many elements.

This is not new mathematics. It excludes no cycle and does not prove the Collatz conjecture or the finite cycles
conjecture. The bound `2^1500` is not claimed as new either: Brox's argument is effective (the Baker–Feldman constant
`C₀` it uses is effectively computable; the paper gives no number), so any explicit lower bound for linear forms in two
logarithms gives an explicit bound; ours comes from the crude constants of `../logs23/`, hence its size.

## How the proof goes, and where it differs from Brox's

1. *Descents are local minima* (`Brox2000/Combinatoire.lean`). Along a cycle, the steps "odd then even" (descents) and
   "even then odd" (an odd term with an even predecessor: a local minimum, `Sdw2005.minCount`) are equally many, since
   the parity sequence is periodic. Over the minimal period, distinct values and terms agree (`../sdw2005/`,
   `Sdw2005/Pont.lean`), so `|Gamma n| = oddCount n p` and `|descSet n| = minCount n p`.
2. *Lemma 2.2*: `2^j C^[j] n ≤ 4^{K_j} n` (`K_j` odd terms among the first `j`), hence `p ≤ 2K`; and
   `2^j C^[j] n = 3^{K_j} n + G_j` with `0 ≤ G_j ≤ j 3^{K_j} 2^j`, hence `n ≤ p 3^K 2^p`.
3. *The inequality*: `Sdw2005.cycle_chain_thm` turns the cycle into a solution of the chain equation with `m` blocks
   (`m` = the number of local minima) and `K` odd terms, and `Sdw2005.lemma7_thm` gives
   `0 < Λ < 2m · 2^{−(δ−1)K/(δ^m − 1)}`, `Λ = (K + L) log 2 − K log 3`, `δ = log₂ 3`. This is the inequality Brox
   obtains in his §§2–5 (his `M ∣ H_j`, the bound for `min 3^{−n} H_j`, and his Lemma 5.1, with the same exponent
   `θ₁ n/(θ^ν − 1)`); here it is taken from `../sdw2005/` (the method of Simons–de Weger 2005, for positive cycles), not
   proved along Brox's lines.
4. *The lower bound* (`Brox2000/Analyse.lean`): `Logs23.two_log_lower_thm` (`|b₁ log 2 − b₂ log 3| ≥ exp(−10^12 ν^5)`
   for `b₂ ≥ 2^334`, `ν = ⌊log₂ b₂⌋ + 1`), in place of Baker–Feldman. If `m < 2 log K` and `K ≥ 2^1500`:
   `e^m < K²` and `δ^200 ≤ e^93` give `(K/δ^m)^200 > K^14`, so `K/δ^m > 2^q` with `q = ⌊7(ν − 1)/100⌋ ≥ 105` (`ν = ⌊log₂ K⌋ + 1 ≥ 1501`), and the
   upper bound of step 3 falls below the lower bound (`5·10^12 (15q + 16)^5 ≤ 2^q` for `q ≥ 105`, by `norm_num`).
5. *Corollary 1.2*: either `ν < 2 log |Γ|`, and Theorem 1.1 applies, or `|Γ| ≤ e^{ν/2} ≤ 3^ν`, and Lemma 2.2 applies.

Not done here: the cycles on the negative integers (phase B; Brox's sign-uniform argument of §§3–5 with his
Lemma 5.1, or a mirror of `../sdw2005/` for `3x − 1`), and Remark 4.1 (`3x + d`).

## Files

| file | content |
|---|---|
| `Brox2000/Brox_Enonces.lean` | the 5 frozen statements (commit f8f331b, alone, before any proof) |
| `Brox2000/Combinatoire.lean` | descents = local minima on a cycle; `\|Γ\|`, `δ(Γ)` as counts of terms; `N ≤ 2K`; `n ≤ N 3^K 2^N` |
| `Brox2000/Analyse.lean` | `chain_K_lt_brox`: a solution of the chain equation with `m < 2 log K` has `K < 2^1500` |
| `Brox2000/Brox.lean` | the proofs of the 5 statements |
| `Brox2000/Axiomes.lean` | `example`s checking each proof against its frozen statement, and `#print axioms` |

## Re-check

From the root of a clone: `cd steiner1978 && lake exe cache get && cd ../brox2000 && ./check.sh`. The script checks
`SHA256SUMS` (5 files), runs `../sdw2005/check.sh` (which runs `../logs23/check.sh`, which re-checks
`../steiner1978/`), compiles the 5 files with `lean -o`, and fails unless the 5 axiom reports are exactly those of the
5 theorems, within `propext`, `Classical.choice`, `Quot.sound`. There is no Lake package here: `env.sh` takes
`LEAN_PATH` from `../steiner1978`.

## Credit

The theorems, the definitions and the strategy (descents, Lemma 2.2, an exponentially small upper bound against a
lower bound for a linear form in two logarithms) are Brox's. Step 3 reuses the formalisation of `../sdw2005/` (after
Simons–de Weger 2005), step 4 the lower bound of `../logs23/` (an interpolation determinant in the spirit of
M. Laurent 1994). Written with Claude (Anthropic); every statement is checked by the Lean kernel.
