# seifert1988 — Seifert's arithmetic of cycles (1988), in Lean

**Status: candidate, in no release yet.** Lean 4.34.0, Mathlib v4.34.0. No hypothesis; axioms `propext`,
`Classical.choice`, `Quot.sound` only.

B. G. Seifert, *On the arithmetic of cycles for the Collatz–Hasse ('Syracuse') conjectures*, Discrete Mathematics 68
(1988), 293–298, DOI [10.1016/0012-365X(88)90121-5](https://doi.org/10.1016/0012-365X(88)90121-5).

**This folder does not prove the Collatz conjecture and proves nothing new about Collatz cycles.** Seifert's theorems
are arithmetic criteria: they say when a given vector of exponents is the vector of a cycle. They exclude no cycle
beyond what is already published. We claim no novelty; the slips listed below may well be known.

**Comparison with the article.** Every reading of "as printed" below was compared on 2026-11-07 with the page images of
the publisher's PDF, at the 400 dpi of the scan, by the AI collaborator (see *Working conditions*): Definition 1.1, the
generator `g`, (e), (d.ε), (1.2), (1.2′), Theorem 1(b) and the remark after it, the examples, Corollaries 1 and 2 with the
difference in the proof of Corollary 1, Theorem 2, `h(j)`, (1.3), (S), (S′) and the acknowledgment. All of them agree. The
comparison also showed two misprints in Theorem 2 and its proof, listed in the table below.

**A published correction?** We looked for one by a web search, which found none. The review zbMATH 0638.10003 was not
read: the automatic check of that site did not let us through.

## The map

For `ε = ±1`, `f_ε(n) = (3n + ε) / 2^k` on the positive odd integers, with `k` the exponent of 2 in `3n + ε`. A cyclic
point `n` has a *length vector* `z = (z(1), …, z(r))`, with `r` the length of its cycle and `z(i)` the exponent of the
step from `f^(i−1)(n)` to `f^i(n)` (Definition 1.1). Seifert sets `d(ε, r)(z) = ε (2^(z(1)+…+z(r)) − 3^r)` and a numerator
`e(r)(z)`.

## The slips

| where | the paper | what holds | Lean |
|---|---|---|---|
| (e), (1.2), (1.2′) | `e(z) = ∑_{j=0}^{r−1} 3^j 2^(z(j+2)+…+z(r))`. With Definition 1.1 this gives 7 on `(1,2)` and 13801 on `(1,1,1,2,1,1,4)`, where the paper's own examples say 5 and 2363; and `139 ∤ 13801` | the printed formula is `e` of the vector read backwards. The formula that fits Definition 1.1 and the examples is `e(z) = ∑_{j=0}^{r−1} 3^j 2^(z(1)+…+z(r−1−j))` | `printed_e_reverse`, `printed_e_examples`, `thm1b_printed_false`, `thm1b_reversed` |
| Remark after Theorem 1 | `e/d(+1, r) = 1` for `z = (1, …, 1)`, "the sequence 1 1 … for `f_1`" | that quotient is `−1`; it is `1` with `d(−1, r)`. The vector of `1 1 …` for `f_1` is `(2, …, 2)` | `remark_constant` |
| Introduction and text after Corollary 2 | to test a vector, "one simply checks" that `e/d` is a positive integer | freeness must stay: `(1,1)` with `ε = −1` passes this test and is not a length vector. With freeness, one divisibility suffices | `free_essential`, `thm1b_single` |
| Corollary 1 | if `z` is a cyclic vector, the vector `z′ ≠ z` with `z(1), z(2)` swapped is not | false for `ε = −1`: `(1,2)` and `(2,1)` are the vectors of 5 and 7. The last step of the proof (`d` odd) does not conclude: `d` odd does not prevent `d ∣ 2^Δ − 1` | `cor1_printed_false`, `cor1_divides`, `cor1_exact` |
| Theorem 2 | exponent `z(2)+…+z(r) − r + 1`. The display prints the numerator `3^r − 3^r`, and the line "Hence" of the proof the denominator `ε(3^r − 2^e)`: misprints, since (1.3) just before has `(3^r − 2^r)` over `ε (2^l − 3^r)` | read as in (1.3), false with Definition 1.1 at `n = 7`, `z = (2,1)`, `ε = −1` (the bound is 5). The exponent that holds is `z(1)+…+z(r−1) − r + 1`, the printed one of the vector read backwards | `thm2_printed_false`, `thm2`, `thm2_plus`, `thm2_reversed` |
| Corollary 2 | (S) and (S′) imply that `2^l − 3^r = ±1` has only the listed solutions | true, and its conclusion holds without (S) or (S′): it is the classical solution of these equations (Levi ben Gerson). The paper's acknowledgment already points to a result of Tijdeman with an equivalent conclusion. As an implication it says nothing beyond that; the step that matters is `solution_gives_cycle` | `cor2_plus`, `cor2_minus`, `gersonides_plus`, `gersonides_minus`, `solution_gives_cycle` |

Theorems 1 and 2 themselves hold once `e` and the exponent are read as above. Their proofs in the paper are the proofs
here. The one thing the paper does not contain is the input that repairs Corollary 1 for `r ≥ 3`.

## Corollary 1, repaired

`cor1_exact`: if `(a, b, w…)` and `(b, a, w…)` with `a ≠ b` are both length vectors, then `ε = −1`, `w` is empty and
`{a, b} = {1, 2}`: the only exception is the cycle (5 7) of `f_{−1}`. `cor1_exact_anywhere` says the same for two adjacent
coordinates at any position.

The proof in the paper gives `d ∣ 2^|a−b| − 1` (`cor1_divides`). To conclude one needs `d` larger than `2^|a−b|`, a lower
bound for `|2^l − 3^r|`:

> `near_miss`: for `r ≥ 3` and every `l`, `2^l ≤ 2^r |2^l − 3^r|`.

For `r ≤ 20000` this is a finite check by the kernel (`allNear_19998`, `decide +kernel`, on the model of
`../steiner1978/Steiner/Fini.lean`); for `r > 20000` it follows from `lam_lower` of [`../logs23/`](../logs23/). The bound is
very weak. Much stronger ones are classical, for instance `|2^x − 3^y| > 2^x e^(−x/10)` for large `x`
(W. J. Ellison, *On a theorem of S. Sivasankaranarayana Pillai*, Séminaire de théorie des nombres de Bordeaux, 1970–1971,
[Numdam](https://www.numdam.org/item/STNB_1970-1971____A10_0/)). We use `lam_lower` because this repository already proves
it, so that nothing is assumed here. This is the reason why this folder depends on `../logs23/`.

## What is proved

Frozen statements: `Seifert1988/Seifert_Enonces.lean`, committed before the proofs (commit 233b2c4, 33 statements). No
statement has changed since; the one later change is the comment above `thm2_printed_false`, corrected on 2026-11-07
after reading the page images. Each statement `X` has a proof `X_thm`; `Seifert1988/Axiomes.lean` checks
`example : X := X_thm` for each.

| statement | content | paper |
|---|---|---|
| `f_maps` | `f_ε` maps positive odd integers to themselves, with a positive exponent | Introduction |
| `d_neg`, `d_perm` | `d(−1) = −d(1)`; `d` is invariant under every permutation | Introduction; proof of Cor. 1 |
| `formula_1_2` | `3^r n + ε e(z) = 2^l f^r(n)` along any piece of orbit | (1.2), repaired |
| `formula_1_2'` | a cyclic point satisfies `d(z) n = e(z)` | (1.2′), repaired |
| `lengthVector_pos` | a length vector is non-empty with positive coordinates | Def. 1.1 |
| `thm1a_unique`, `thm1a_rotate` | a cyclic point is determined by its vector; `f^k(n(z)) = n(g^k z)` | Thm 1(a) |
| `thm1b` | `z` is a length vector iff α) free, β) `d > 0`, γ) `⟨d⟩` contains the ideal generated by the `e(g z)` | Thm 1(b), with `e` |
| `thm1b_single` | the same with the single condition `d ∣ e(z)` in γ) | the "computational criterion", repaired |
| `free_essential` | `(1,1)`, `ε = −1`: `d > 0`, `d ∣ e`, not a length vector | remark after Thm 1 |
| `examples` | 5 and 17 with their `z`, `e`, `d`; the fixed point 1 for each `f_ε` | Examples |
| `remark_constant` | `e` and `d` on `(1,…,1)` and `(2,…,2)` | remark after Thm 1, corrected |
| `printed_e_reverse`, `printed_e_examples` | the printed (e) is `e` of the reversed vector; 7, 13801, `139 ∤ 13801` | (e) |
| `thm1b_printed_false`, `thm1b_reversed` | Thm 1(b) ⇒ γ) fails with the printed (e); it holds for the reversed vector | Thm 1(b), as printed |
| `cor1_difference_printed`, `cor1_difference` | `e(z) − e(z′)` for the printed (e) and for `e` | proof of Cor. 1 |
| `cor1_printed_false`, `cor1_divides` | see above | Cor. 1 |
| `near_miss`, `cor1_exact`, `cor1_exact_anywhere` | see above | not in the paper |
| `solution_gives_cycle` | a solution of `2^l − 3^r = ε` with `r ≥ 2` gives the length vector `(l−r+1, 1, …, 1)`, since `d = 1` | proof of Cor. 2 |
| `cor2_plus`, `cor2_minus` | Corollary 2, by the paper's route | Cor. 2 |
| `gersonides_plus`, `gersonides_minus` | the same conclusions without (S), (S′) | not in the paper |
| `thm2`, `thm2_plus` | `d n ≤ 2^H (3^r − 2^r)`; for `ε = 1`, `d n ≤ 2^H (2^l − 2^r)`, with `H = z(1)+…+z(r−1) − r + 1` | Thm 2, repaired |
| `thm2_printed_false`, `thm2_reversed` | the counterexample `n = 7`; `H` is the printed exponent of the reversed vector | Thm 2, as printed |

Modelling choices, all visible in `Seifert_Enonces.lean`:
* The length `r` of a cycle is the minimal period (`Function.minimalPeriod`), and a cyclic point is positive and odd.
* Freeness is `∀ k, 0 < k < r → z.rotate k ≠ z`. The ideal in γ) is an `Ideal ℤ`.
* In `thm1a_rotate`, `k` is a natural number; the paper says "an integer", which adds nothing on a cycle.
* (S′) is stated for positive odd `n`, the domain of `f`; the paper says "positive integer".
* Theorem 2 is stated with `d n ≤ …` rather than a quotient; `d > 0` comes from `thm1b`. In `H` the subtraction is on
  natural numbers; it does not truncate on a length vector, since every coordinate is at least 1 (`sum_dropLast_ge`).
  In `thm2_printed_false` it reads `1 − 1 = 0`.

## How it is proved

* `Seifert1988/Algebre.lean`: `e(a :: w) = 3^|w| + 2^a e(w)` and `e(u ++ v) = 3^|v| e(u) + 2^(sum u) e(v)`; the transport
  `2^a e(w ++ [a]) = 3 e(a :: w) + ε d(a :: w)`, which carries a divisibility from one rotation to the next; `d` is odd and
  prime to 3.
* `Seifert1988/Dynamique.lean`: (1.2) and (1.2′) by induction along the orbit; Theorem 1, with the construction of the
  points `e(g^k z)/d` of the cycle for the converse.
* `Seifert1988/Corollaires.lean`: the examples, by computation; the statements on the printed (e); Corollaries 1 and 2;
  Theorem 2; the two equations of Levi ben Gerson, by reduction modulo 8 and factorisation.
* `Seifert1988/Voisins.lean`: `near_miss` and the repaired Corollary 1.

## Re-checking

Prerequisites as for [`../logs23/`](../logs23/README.md#re-checking). From the root of a fresh clone of the repository:

```bash
cd steiner1978
lake exe cache get
cd ../seifert1988
./check.sh
```

`./check.sh` checks `SHA256SUMS` (the Lean sources of `Seifert1988/`), runs `../logs23/check.sh` (which itself runs
`../steiner1978/check.sh`), compiles `Seifert1988/*.lean` one by one with `lean -o` (`LEAN_PATH` from `env.sh`: this folder's
build directory, then the `LEAN_PATH` of `../logs23`; this folder has no Lake package of its own and `lake build` is not
used), fails on any error or `sorry` warning in these files, and reads the axiom report of `Seifert1988/Axiomes.lean`: it
fails unless the reports are exactly those of the 33 theorems listed in `check.sh`, each with standard axioms only.
Recorded report: `axioms/Seifert_Axiomes.txt`.

These commands were run on 2026-11-06 from a fresh clone of commit 2dae56b (`git clone --no-local` of a local copy of the
repository; the later commits change no Lean source, `check.sh`, `env.sh` or `SHA256SUMS`), on a machine with 16 GB of
memory where Lean 4.34.0 was already installed and Mathlib's prebuilt files were already in the local cache. They took
441 s in all. `../steiner1978/check.sh` read its 12 axiom reports, `../logs23/check.sh` its 15 and `./check.sh` its 33, all
with standard axioms only; the 33 were the same as the recorded ones.

## Working conditions

As for the rest of this repository (root README, *Working conditions, disclosed*): the development is carried out with
an AI collaborator (Claude), and no human mathematician has audited these proofs. The Lean kernel checks the proofs. It
does not check that the statements say what the paper says: read `Seifert1988/Seifert_Enonces.lean` for that.
