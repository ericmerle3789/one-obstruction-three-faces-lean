# Numerical recomputations (Python)

Independent recomputations of the numerical points of `../README.md`, in Python 3 with the standard library only.
They are not proofs: everything claimed as *proved* in `../README.md` is checked by the Lean kernel. Each script is
deterministic; its recorded output is next to it (`<name>.out.txt`).

```bash
cd lagarias1990/checks
python3 L1990_audit_numerique.py          # compare with L1990_audit_numerique.out.txt
```

| script | recomputes |
|---|---|
| `L1990_audit_numerique.py` | Tables 2.1, 2.2, 3.1 (48 of 50 rows as printed); p. 41 (`min_l |2ⁿ − 3^l|/2ⁿ` at the periods 100, 106, 136); the constants `φ`, `H(φ)`, `α_c`, `β_c`; p. 43 (number of necklaces with `n` ones of length `2n` against `n^{−1}C(2n,n)`, `n ≤ 5, 10, 20, 40`); (4.4); the example `5/(2^m − 9)`; `Z(d,k)` and the sign of `T_k`; p. 37; Theorem 3.5 for `n ≤ 12`; Theorem 4.1 for small `n` |
| `L1990_table31_details.py` | Table 3.1, rows `k = 35` and `k = 73`; `α_c` with the printed (truncated) `H(φ) ≐ 0.949955` |
| `L1990_certificats_table31.py` | the non-periodicity certificates used for the minimality of the two corrected rows of Table 3.1 |
| `L1990_contre_verif_redteam.py` | two of the first review's points, p. 48 (twice) and p. 44: R1, the printed bound `m·2^{n−m}` of Theorem 4.1 fails only for `M = 2` among `n ≤ 12`, `2 ≤ M < min(2000, 3ⁿ)` (`M = 1` is not tested); R2, at most `max(1, m)` heads per class (`n ≤ 9`); R3, the minimum of the negative cycles of `−5` and `−17` is `≡ 2 (mod 6)`. Its docstring says "Red Team remarks": it predates the naming of `../README.md`, where the passes before release are called adversarial passes |
| `L1990_mots_primitifs_2n4.py` | (2.4), (2.5), Table 2.1 by brute force for `n ≤ 16`; the arithmetic of `2n⁴` in Theorem 4.2 |
| `L1990_rt4_verifications.py` | p. 44: the inequality `k_m/2 ≥ (2^{5n} − 2ⁿ)/(3ⁿ − 2ⁿ)` for `n ≤ 14`, `m = 4n` (P1) and the denominator `k_m` (P2); p. 37: the exponent `k+1` (P3); p. 39: the sign of `δ` (P4); p. 44: `N(v)` even (P5); p. 34: `k = 5` (P6) |
| `L1990_rt3_eq413_terme_suivant.py` | (4.13): the correction to `Σ_{n ≤ β log₂ x} 2ⁿ/n − 2x^β/(β log₂ x)` is of order `x^β/(log x)²`, not `O(x^{β/2})` (`β = 1/2, 1, 11/10, 2`; `x = 2^{100}, 2^{200}, 2^{400}`) |
| `L1990_rt2_eq413_fenetres.py` | the second inequality of (4.13) for `β = 1/2, 1, 2` and `x = 2^{100}`; the count of normal windows in the proof of Theorem 4.2 (`M = 7`, and a search in the range `2n²·2^m ≤ M < 4n²·2^m`, `n ≤ 9`, `m ≤ 3`) |

The prefixes `rt2`, `rt3`, `rt4` (and "Red Team pass 2, 3, 4" in the docstrings) name the adversarial pass before
release during which each script was written. The scripts are copied unchanged from the lab's internal log, where each one was run once with predictions
written before the run; `L1990_audit_numerique.py` mentions its prediction file, which stays in that log.
