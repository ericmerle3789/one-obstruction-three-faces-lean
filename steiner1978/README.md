# Steiner 1978 in Lean 4

R. P. Steiner, *A theorem on the Syracuse problem*, Proceedings of the 7th Manitoba Conference on Numerical
Mathematics and Computing (Winnipeg, 1977), Congressus Numerantium 20, Utilitas Math., 1978, pp. 553–559
(MR 80g:10003).

> **What this is.** A formalisation of a classical theorem from 1978: the only circuit on the positive integers
> that is a cycle of the `3x+1` map is `{1, 2}` — here under a named hypothesis (Rhin's bound), and without any
> hypothesis for at most 20000 odd terms. It proves nothing new about Collatz cycles.
> **The original paper (Congr. Numer. 20, 1978) could not be accessed and was not read; the statements and the proof
> are reconstructed from Steiner 1981 (Fibonacci Quart. 19, the analogous problem for `q = 5` and `q = 7`),
> Lagarias's annotated bibliography and Simons–de Weger 2005 (read in their version 1.44 of 2010), §1.4 and
> Lemma 12** (see *Sources*). Of the four steps of Steiner's proof, as Simons and de Weger describe it, the
> inequality and the convergent property are formalised; the rest is replaced by Rhin's lower bound for
> `|x log 2 + y log 3|` instead of Baker's, as in their Lemma 12, and by an exact check of each small `k`.

**Status (2026-10-21).**
- **Kernel-checked: 12 frozen statements, all proved** (`check.sh` checks that there are 12 axiom reports, one per
  theorem).
- **Named hypothesis:** `H_Rhin`, the case `u₀ = 0` of Rhin's inequality (7). It enters only as the premise
  `H_Rhin → …` of six statements, never as an axiom.
- **Without any hypothesis:** the correspondence between circuits and Davison's equation, the inequality, the
  convergent step, and the theorem for `k ≤ 20000` odd terms; hence a circuit-cycle on the positive integers other
  than `{1, 2}` would start at `n ≥ 2^20001 − 1`. The bound `k ≤ 20000` is a finite check certified by the kernel.
  It uses no computer verification of the conjecture, and it is far weaker than the bounds that do: Hercher 2023
  (arXiv 2201.00406v3, p. 2) reports "the current K > 7.2 · 10^10" odd terms for every nontrivial cycle. We make
  no claim of novelty.
- **0 `sorry`** in the proofs (one unused marker in a copied dependency, see *Dependencies*); **0 `native_decide`**:
  the finite check uses `decide +kernel`.
- **Axioms:** only `propext`, `Classical.choice`, `Quot.sound` (log in [`axioms/`](axioms/)).
- **Lean 4.34.0, Mathlib v4.34.0**, i.e. after the fix of the kernel soundness bug
  [lean4#14576](https://github.com/leanprover/lean4/issues/14576) (v4.32.2).

## How to check

```bash
cd steiner1978
lake exe cache get
./check.sh
```

`lake build` is not supported (there is no `Steiner.lean` root file); use `check.sh`, which needs `python3`. It
first checks the sources against `SHA256SUMS`, then compiles the 7 files one by one with `lake env lean`, in
dependency order. It then reads the `#print axioms` output of `Steiner/Axiomes.lean`, and fails if any theorem
depends on an axiom other than the three above, or if the number of reports is not 12. It was run from a clean
build on 2026-10-21 (6 to 11 minutes on an M1 Pro once Mathlib is cached, mostly loading Mathlib).

## Sources

| key | account | what we take from it |
|---|---|---|
| [La] | J. C. Lagarias, *The 3x+1 problem: an annotated bibliography (1963–1999)*, arXiv math/0309224v13 (2011), entries 158 (Steiner 1978) and 48 (Davison 1977) | entry 158 (p. 60): the statement, circuits, Davison's equation, "the only solution to this equation in positive integers is (k, l, h) = (1, 1, 1)", and a bracketed remark on the nonpositive integers; entry 48 (p. 22): `h = (n+1)/2^k`, `n` the smallest odd number in the cycle |
| [SdW] | J. Simons, B. de Weger, *Theoretical and computational bounds for m-cycles of the 3n+1 problem*, Acta Arith. 117 (2005) (their version 1.3); we use version 1.44 (2010), §1.4 (pp. 3–4) and Lemma 12 (pp. 10–11) | the four steps of Steiner's proof (p. 3); the inequality `0 < (k+ℓ) log 2 − k log 3 < 1/x_min` (p. 4); the use of Rhin's bound |
| [St81] | R. Steiner, *On the "Qx + 1 problem," Q odd*, Fibonacci Quart. 19 (1981), 285–288 | the analogous problem for `q = 5` and `q = 7`, with a reference to the 1978 paper ([La], entry 159, p. 60: "Baker's method is again used, as in Steiner (1978)"): inequality (4), "if k ≥ 4, ℓ/k must be a convergent" and Baker's theorem (p. 286), then the continued fraction (p. 287) |
| [Rh] | G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Progress in Math. 71 (1987), 155–164 | inequality (7), see *Named hypothesis* |

## The statements

`T` is the map `x ↦ x/2` (`x` even), `(3x+1)/2` (`x` odd) on `ℤ`. `CircuitCycle n k l`: the iterates
`n, T(n), …, T^{k−1}(n)` are odd, the next `l` are even, and `T^{k+l}(n) = n`. `DavisonEq k l h`:
`(2^{k+l} − 3^k)·h = 2^l − 1`. `Λ = (k+l) log 2 − k log 3`.

| account | Lean | hypothesis | content |
|---|---|---|---|
| [La], entries 158 (p. 60) and 48 (p. 22): circuit-cycles correspond to the solutions of Davison's equation, `h = (n+1)/2^k` | `circuit_iff` | — | for `k ≥ 1`: `CircuitCycle n k l ↔ ∃ h, n + 1 = 2^k h ∧ DavisonEq k l h`, for every `n ∈ ℤ` |
| [SdW] §1.4, p. 4; [St81] (4), p. 286, for `q = 5` | `ineq4` | — | a positive solution has `0 < Λ < 1/(2^k h − 1) ≤ 1/(2^k − 1)` (`2^k h − 1` is the smallest element `n`) |
| [SdW] §1.4, p. 4: "(k+ℓ)/k must be a convergent of δ for k ≥ 5" | `convergent4` | — | for `k ≥ 4`, `0 < Λ < 1/(2^k − 1)` makes `(k+l)/k` a convergent of `log₂ 3` (Mathlib's `Real.convergent`, by Legendre's theorem) |
| [SdW] §1.4, p. 3: an upper bound for `k` from Baker's theorem | `rhin_k_le` | `H_Rhin` | every solution with `k ≥ 1`, `l ≥ 1`, `h ≠ 0` has `k ≤ 108` |
| — | `steiner_small` | — | for `1 ≤ k ≤ 20000`, the only positive solution is `(1, 1, 1)` |
| [La], entry 158, p. 60: the only positive solution is `(1, 1, 1)` | `steiner` | `H_Rhin` | as stated |
| [La], entry 158, p. 60: "the only circuit on the positive integers that is a cycle is {1, 2}" | `steiner_cycle` | `H_Rhin` | for `n > 0`, `k ≥ 1`: `CircuitCycle n k l → n = 1 ∧ k = 1 ∧ l = 1` |
| — | `steiner_cycle_small` | — | the same for `k ≤ 20000` |
| — | `circuit_large` | — | a circuit-cycle with `n > 0`, `k ≥ 1`, `n ≠ 1` has `n ≥ 2^20001 − 1` |
| [La], entry 158, p. 60, in brackets: on the nonpositive integers, the cycles `{−1}` and `{−5, −7, −10}`, the solutions `(k, 0, 0)` and `(2, 1, −1)` | `steiner_int`, `steiner_cycle_int` | `H_Rhin` | for `k ≥ 1` and `h ∈ ℤ`, every solution is `l = h = 0`, `(1, 1, 1)` or `(2, 1, −1)`; every circuit-cycle on `ℤ` starts at `n = −1` (`l = 0`), `n = 1` or `n = −5` |
| — | `tstar_circuit` | `H_Rhin` | the open target T★ of `Labo/Blueprint.lean` holds for the words `1^k 0^l` |

[La]'s bracketed remark announces "exactly three circuits that are cycles on the non-positive integers" and names
two, `{−1}` and `{−5, −7, −10}`; under `H_Rhin`, `steiner_cycle_int` allows only these two on the nonpositive
integers.

The statements are frozen in `Steiner/Steiner_Enonces.lean`, with a comparison with the accounts in its header;
they were committed without any proof (commit 7fd7873, with the copied `Labo/Blueprint.lean` and the Lake files).
`Steiner/Axiomes.lean` checks `example : X := X_thm` for each of them.

## Named hypothesis

| name | content | source |
|---|---|---|
| `H_Rhin` | for integers `u₁, u₂` with `H = max(|u₁|, |u₂|) ≥ 2`: `H^(−13.3) ≤ |u₁ log 2 + u₂ log 3|` | [Rh], Proposition p. 160 (the page given by [SdW] and Simons 2022), inequality (7), case `u₀ = 0` |

- Rhin's (7) reads: for integers `u₀, u₁, u₂` with `H = max(|u₁|, |u₂|) ≥ 2`, `|u₀ + u₁ log 2 + u₂ log 3| ≥ H^(−13.3)`.
  The lab read it in the author's copy of the paper on 2026-09-26; we could not open that copy again for this
  release. [SdW] (Lemma 12: "We apply the Proposition on p. 160 of [Rh] with u₀ = 0, H = u₁ = K + L, and u₂ = −K")
  and J. L. Simons, arXiv:2205.10582 (in the proofs of Lemma 10: `|Λ| ≥ [2K + L]^−13.3`, with `H = |u₁|`, and of
  Lemma 12: `|Λ| ≥ [3K + 2L]^−13.3`, with `H = |u₂|`) apply it with `u₀ = 0`.
- Only the case `u₀ = 0` is assumed; it is applied with `u₁ = k + l`, `u₂ = −k`. The other statements use `H_Rhin`
  only through `rhin_k_le`, whose proof applies it only for `k ≥ 109`, so with `H = k + l ≥ 110`.
- `checks/` (P6, a corroboration, not a proof): for `2 ≤ H ≤ 3000`, `min |u₁ log 2 + u₂ log 3|·H^13.3 ≈ 2901`.

## The finite check

For a positive solution, `D = 2^{k+l} − 3^k` satisfies `0 < D` and `D(2^k − 1) ≤ 3^k − 2^k`; this leaves one
possible value of `k + l`, the least `L` with `2^L > 3^k`. For a negative solution (`h ≤ −1`),
`E = 3^k − 2^{k+l}` satisfies `0 < E` and `E(2^k + 1) ≤ 3^k − 2^k`, which leaves `L − 1`. `Steiner/Fini.lean`
tests both candidates for every `2 ≤ k ≤ 20000` (`allChk_20000`, `decide +kernel`): each one is excluded,
except the negative candidate at `k = 2`, where `(2, 1, −1)` is a solution; that test is skipped. The case
`k = 1` is treated directly in the proofs. `L` is computed from 40 digits of `log₂ 3`, and the check re-checks
`2^{L−1} ≤ 3^k < 2^L`, so a wrong approximation could only make the computation fail.

`rhin_k_le` shows that `H_Rhin` leaves only `k ≤ 108`, well inside the checked range.

## How the Lean proof follows the account

[SdW] §1.4 lists four steps in Steiner's proof. In Lean:
1. the inequality for `(k+ℓ)/k`: `ineq4`;
2. a lower bound for `k`, then `(k+ℓ)/k` is a convergent: `convergent4`, which assumes `k ≥ 4` instead of proving a
   lower bound (the finite check plays that role);
3. an upper bound for `k` from Baker's theorem: `rhin_k_le`, from Rhin's bound;
4. a lower bound for the partial quotients, then a computation of the continued fraction of `log₂ 3`: replaced by
   the finite check, which tests each `k ≤ 20000` directly.

The proof of `steiner` uses neither `ineq4` nor `convergent4`: it uses `rhin_k_le`, whose proof derives the
inequality again (lemmas `pos_facts`, `Lam_pos_le`), and the finite check.

## Not formalised

- Steiner's own step 3 (Baker's theorem; [La] and [St81] cite A. Baker, *Transcendental Number Theory*, p. 45)
  and step 4 (the continued fraction of `log₂ 3` up to the resulting bound; in [St81] the bound is `10^201` for
  `q = 5`): replaced, see above.
- The numbers of the 1978 paper: its text was not read.
- Steiner's map: [St81] says that the 1978 paper studied `f(n) = (3n+1)/2` (`n` odd, `n > 1`), `n/2` (`n` even),
  `f(1) = 1`. The statements here use `T`, with `T(1) = 2`, as [La] does.
- The circuit map `n ↦ n*` on the positive odd integers and the monotone runs of [St81] (Theorems 1 and 5), known
  to us for `q = 5, 7` only.

## The header of the frozen file

The header of `Steiner/Steiner_Enonces.lean` is frozen with the statements (its SHA-256 is fixed). It cites [La] as
entry 158; the formula `h = (n+1)/2^k` of its second row is in entry 48 (Davison 1977) of the same bibliography.
Its rows cite sections and equation numbers, not pages; the table of *The statements* gives the pages.
Its first row says that `1 ≤ k` is a hypothesis of each statement: `convergent4` assumes `4 ≤ k`, and
`tstar_circuit` assumes `true ∈ oneBlock k l`, which amounts to `1 ≤ k`.

## Layout

| file | content |
|---|---|
| `Steiner/Steiner_Enonces.lean` | the frozen statements and `H_Rhin`, with the comparison table in the header |
| `Steiner/Dynamique.lean` | `circuit_iff` (odd and even runs of `T`) |
| `Steiner/Fini.lean` | the finite check |
| `Steiner/Analyse.lean` | `ineq4`, `convergent4`, `rhin_k_le` |
| `Steiner/Principal.lean` | `steiner_small`, `steiner`, `steiner_int`, the circuit statements, `tstar_circuit` |
| `Steiner/Axiomes.lean` | statement checks and `#print axioms` |
| `checks/` | a Python recomputation of the numerical points (not a proof; see `checks/README.md`) |
| `Labo/Blueprint.lean` | copied from `hh1997/` (see *Dependencies*) |

## Related work

- **ccchallenge** entry `Steiner1978`: status `not_started`, no formalisation (public API, 2026-10-21).
- **Hercher 2023.** [PhilNorfleet/Hercher2023_lean](https://github.com/PhilNorfleet/Hercher2023_lean)
  (ccchallenge entry `Hercher2023`, status `waiting_to_be_audited`) formalises Hercher's *There are no Collatz
  m-Cycles with m ≤ 91*. Its main theorem, `no_m_cycle_le_82` (read on 2026-10-21), excludes m-cycles with
  `m ≤ 82` under two external hypotheses; one bounds the number `K` of odd terms of the cycle by `1.4784·m·δ^m`. At `m = 1`
  this hypothesis already gives `K ≤ 2`, so its case `m = 1` is not Steiner's theorem.
- **This repository.** `hh1997/` uses the same map `T` (`LaboBP.T`).

## Dependencies

`Labo/Blueprint.lean` is copied unchanged from `hh1997/` (commit 36d5136; sha256
`c397d06ecff993125417ea28750cd82d24dc31461de6bfa15435082d49c185ac`, as in `hh1997/SHA256SUMS`). It provides `T`, the
parity-word functions `C` and `d`, the predicate `TrivialWord`, and the target T★ (`Tstar`). It contains one `sorry`: the marker
`Tstar_open` for the open statement T★. It is never used; the axiom report of every theorem here excludes
`sorryAx`.
