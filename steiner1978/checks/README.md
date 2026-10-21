# Numerical recomputation (Python)

One script, `ST1978_phase1_audit.py` (Python 3 and `mpmath`), with its recorded output next to it
(`ST1978_phase1_audit.out.txt`). It was written and run before the Lean proofs, to plan them. It is not a proof:
everything claimed as *proved* in `../README.md` is checked by the Lean kernel. It is deterministic.

```bash
cd steiner1978/checks
python3 ST1978_phase1_audit.py          # compare with ST1978_phase1_audit.out.txt
```

| point | recomputes | Lean counterpart |
|---|---|---|
| P1 | for `1 ≤ k ≤ 20000` and `L` the least integer with `2^L > 3^k`, the inequality `(2^L − 3^k)(2^k − 1) ≤ 3^k − 2^k` holds only at `k = 1`; for a larger `L`, `2^L − 3^k > 3^k` | `allChk_20000`, `pos_exclude` |
| P2 | for `1 ≤ k ≤ 20000` and `L` one less, `(3^k − 2^L)(2^k + 1) ≤ 3^k − 2^k` holds only at `k = 2` | `allChk_20000`, `neg_exclude` |
| P3 | the solutions of Davison's equation with `1 ≤ k ≤ 40`, `0 ≤ l ≤ 40`: `(1, 1, 1)`, `(2, 1, −1)`, and `h = 0` when `l = 0` | `steiner_int` |
| P4 | `k·A // B + 1` (`A/B`: 40 digits of `log₂ 3`) is the least `L` with `2^L > 3^k`, for every `k ≤ 20000` | `Lk` (re-checked by `posOK` in Lean) |
| P5 | the largest `k` with `2^k − 1 < (2k)^14` is 108; the largest `k` with `2^k − 1 < L^13.3` (same `L`) is 96 | `big`, `rhin_k_le` |
| P6 | `min |u₁ log 2 + u₂ log 3|·H^13.3` over `2 ≤ H = max(|u₁|, |u₂|) ≤ 3000` is about 2901, at `(u₁, u₂) = (2, −1)`: a corroboration of the hypothesis `H_Rhin` in this range, not a proof of it | `H_Rhin` |
| P7 | `2k < (2^k − 1) ln 2` holds for `4 ≤ k ≤ 200` and fails for `k ≤ 3` | `three_mul_add_one_le_two_pow`, `convergent4` |

The script is copied unchanged from the lab's internal log, where it was run once with predictions written before
the run (all confirmed). Its docstring says "phase 1" and its points are numbered P1–P7 as in that log.
