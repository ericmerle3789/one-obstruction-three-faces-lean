# brox2000 — Brox 2000, *Collatz cycles with few descents* (Theorem 1.1, Corollary 1.2, Lemma 2.2)

**Status: in release v1.9 of this repository** (its first release that contains this folder), archived on Zenodo;
concept DOI [10.5281/zenodo.23498095](https://doi.org/10.5281/zenodo.23498095), which resolves to the latest version;
the DOI of v1.9 is listed on the Zenodo record. Phase A (positive cycles) and phase B (all cycles, on `ℤ`).
Lean 4.34.0, Mathlib v4.34.0; uses the build of `../steiner1978/` and the modules of `../logs23/` and `../sdw2005/`.

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

Brox's three results for **all** Collatz cycles, on `ℤ` (phase B, added later the same day), and before that for the
cycles on the positive integers, on `ℕ` (phase A).

### Phase B: Brox's setting, on `ℤ`

With Brox's `T` on `ℤ` (`T x = x/2` for `x` even, `(3x + 1)/2` for `x` odd; `Brox2000/BroxZ_Enonces.lean`), for `x`
on a cycle of `T` (`Function.minimalPeriod T x > 0`): `GammaZ x` = the distinct odd values `T^[j] x` over the minimal
period (Brox's `Γ`), `descSetZ x` = the `y ∈ GammaZ x` with `T y` even (his descending elements: for `y` odd, `T y` is
even if and only if `4 ∣ 3y + 1`). The cycle `{0}` has no odd element.

| statement (`Brox2000/BroxZ_Enonces.lean`, frozen before the proofs) | content | in the paper |
|---|---|---|
| `lemma22_Z` | `x ≠ 0` on a cycle: `minimalPeriod T x ≤ 2 · \|GammaZ x\|` | Lemma 2.2, `k ≤ 2n` |
| `lemma22_finite_Z` | for every `K`, finitely many `x ∈ ℤ` lie on a cycle with `\|GammaZ x\| ≤ K` | Lemma 2.2, second sentence |
| `thm11_Z_explicit` | `\|descSetZ x\| < 2 log \|GammaZ x\|` implies `\|GammaZ x\| < 2^1500` | Theorem 1.1, with an explicit bound |
| `thm11_Z` | finitely many `x ∈ ℤ` lie on a cycle with `\|descSetZ x\| < 2 log \|GammaZ x\|` | **Theorem 1.1** |
| `cor12_Z` | for every `ν`, finitely many `x ∈ ℤ` lie on a cycle with `\|descSetZ x\| ≤ ν` | **Corollary 1.2** |

On the three known cycles on the negative integers, those of `−1`, `−5`, `−17`, `|Γ| = 1, 2, 7` and
`δ(Γ) = 0, 1, 2` (counted by hand on the orbits of `T` printed with `#eval`; `GammaZ` is not computable; not part of
the check).

### Phase A: the positive cycles, on `ℕ`

With `C = Sdw2005.C` (`C n = n/2` for `n` even,
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

All 10 statements (5 of phase B, 5 of phase A) are proved, with no hypothesis, and depend only on the axioms
`propext`, `Classical.choice`, `Quot.sound` (`axioms/Brox2000_Axiomes.txt`). "Finitely many integers on such
cycles" and "finitely many such cycles" say the same thing, since a cycle has finitely many elements.

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

Phase B (`Brox2000/Miroir*.lean`, `Brox2000/BroxZ.lean`):

6. *Conjugacies*: `T (n : ℤ) = C n` and `T (−n) = −D n` for `n : ℕ`, with `D(y) = y/2` (`y` even), `(3y − 1)/2`
   (`y` odd); so the cycles of `T` on the positive (negative) integers are those of `C` (of `D`), with the same minimal
   period, the same `Γ` and the same descending elements. Phase A covers the positive side.
7. *The mirror chain* (`Brox2000/MiroirCycles.lean`, adapted from `../sdw2005/Sdw2005/Cycles.lean`): a cycle of `D`
   through `n > 1` gives `3^{k_i} a_i + 1 = 2^{l_i} x_{i+1}` with local minima `x_i = 2^{k_i} a_i + 1`
   (`D 1 = 1`: the fixed point `1` of `D`, Brox's `−1`, has `|Γ| = 1` and is treated apart). With `Y_i = 2^{k_i} a_i`,
   `Λ' = K log 3 − (K + L) log 2 = Σ (log(1 + 1/Y_i) − log(1 + 1/(3^{k_i} a_i)))`, so `0 < Λ' < Σ 1/Y_i`; and
   `Y_{i+1} < 3^{k_i} a_i ≤ Y_i^δ`, so `Y_i ≥ 2^E` and `Λ' < m · 2^{−E}` (`Brox2000/MiroirChaine.lean`; the mirror of
   Lemmas 4, 6, 7 of Simons–de Weger, written here). Steps 1, 2 and 5 then go as in phase A
   (`Brox2000/MiroirCombinatoire.lean`, `Brox2000/BroxZ.lean`), and step 4 too (`chain_K_lt_brox_M`, with `m` in
   place of `2m`).

Not done here: Brox's own route (§§2–5: `M ∣ H_j`, his Lemma 5.1), which is replaced by the chain of Simons–de Weger
and its mirror, and Remark 4.1 (`3x + d`).

## Files

| file | content |
|---|---|
| `Brox2000/Brox_Enonces.lean` | the 5 frozen statements of phase A (commit f8f331b, the only Lean file of that commit, with `env.sh` and `lean-toolchain`; before any proof) |
| `Brox2000/Combinatoire.lean` | descents = local minima on a cycle; `\|Γ\|`, `δ(Γ)` as counts of terms; `N ≤ 2K`; `n ≤ N 3^K 2^N` |
| `Brox2000/Analyse.lean` | `chain_K_lt_brox`: a solution of the chain equation with `m < 2 log K` has `K < 2^1500` |
| `Brox2000/Brox.lean` | the proofs of the 5 statements of phase A |
| `Brox2000/BroxZ_Enonces.lean` | the 5 frozen statements of phase B, on `ℤ` (commit 4ce3d44, alone, before the proof files; see the note below) |
| `Brox2000/MiroirChaine.lean` | the chain equation of `3x − 1` (`ChainSolM`), Lemmas 4, 6, 7 mirrored, `chain_K_lt_brox_M` |
| `Brox2000/MiroirCycles.lean` | a cycle of `D` through `n > 1` gives a solution of `ChainSolM` |
| `Brox2000/MiroirCombinatoire.lean` | phase A's combinatorics for `D` |
| `Brox2000/BroxZ.lean` | the conjugacies and the proofs of the 5 statements of phase B |
| `Brox2000/Axiomes.lean` | `example`s checking each proof against its frozen statement, and `#print axioms` (10 reports) |

*Note on phase B (2026-11-08).* `Brox2000/BroxZ_Enonces.lean` was written before any proof file of phase B and not
changed afterwards, but it was committed after those proof files had been drafted (they were written while the full
check of phase A was running); it is committed alone, before them.

## Re-check

From the root of a clone: `cd steiner1978 && lake exe cache get && cd ../brox2000 && ./check.sh`. The script checks
`SHA256SUMS` (10 files), runs `../sdw2005/check.sh` (which runs `../logs23/check.sh`, which re-checks
`../steiner1978/`), compiles the 10 files with `lean -o`, and fails unless the 10 axiom reports are exactly those of
the 10 theorems, within `propext`, `Classical.choice`, `Quot.sound`. There is no Lake package here: `env.sh` takes
`LEAN_PATH` from `../steiner1978`.
This folder was re-run from a fresh GitHub clone of commit 9077bda (2026-11-08), with Lean 4.34.0 already installed
and Mathlib's download cache already filled: exit 0, 30 minutes including the clone, `lake exe cache get` and the runs
of `steiner1978/check.sh`, `logs23/check.sh` and `sdw2005/check.sh` that `brox2000/check.sh` starts, 12 + 15 + 13 + 10
axiom reports (`steiner1978/`, `logs23/`, `sdw2005/`, `brox2000/`), `sdw2005/axioms/Sdw2005_Axiomes.txt` and
`brox2000/axioms/Brox2000_Axiomes.txt` identical byte for byte to the axiom lines of the logs of the run.

## Credit

The theorems, the definitions and the strategy (descents, Lemma 2.2, an exponentially small upper bound against a
lower bound for a linear form in two logarithms) are Brox's. Step 3 reuses the formalisation of `../sdw2005/` (after
Simons–de Weger 2005), step 4 the lower bound of `../logs23/` (an interpolation determinant in the spirit of
M. Laurent 1994); step 7 mirrors `../sdw2005/` for `3x − 1`. Written with Claude (Anthropic); every statement is checked by the Lean kernel.
