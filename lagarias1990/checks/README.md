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
| `L1990_table31_details.py` | Table 3.1, rows `k = 35` and `k = 73`; `α_c` with `H(φ)` rounded as printed |
| `L1990_certificats_table31.py` | the non-periodicity certificates used for the minimality of the two corrected rows of Table 3.1 |
| `L1990_contre_verif_redteam.py` | the first review's three points: the printed bound `m·2^{n−m}` of Theorem 4.1 fails only for `M = 2`; at most `max(1, m)` heads per class (`n ≤ 9`); the minimum of the negative cycles of `−5` and `−17` is `≡ 2 (mod 6)` |
| `L1990_mots_primitifs_2n4.py` | (2.4), (2.5), Table 2.1 by brute force for `n ≤ 16`; the arithmetic of `2n⁴` in Theorem 4.2 |

The scripts are copied unchanged from the lab's internal log, where each one was run once with predictions
written before the run; `L1990_audit_numerique.py` mentions its prediction file, which stays in that log.
