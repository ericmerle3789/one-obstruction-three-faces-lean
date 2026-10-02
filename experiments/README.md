# Verification scripts — Merle side

> **Erratum and index (2026-10-02).** The table below covers REQ-MATH-001–012 only; later
> scripts (013–067, run_048–run_130) are documented in their own headers and in the shared
> LEDGER and rounds. Scripts 001–012 have no committed output. Dated files are kept as written;
> read them with these corrections:
> - **μ = 5.125 is Salikhov's (2007) irrationality measure of ln 3, not of log₂3.** Where
>   `test_REQ-MATH-001` (the 3693 canary), `-004`, `-029`, `-030` and `ARBRE_JUSQU_A_LA_RACINE.md`
>   use it for log₂3, it is misapplied. The re-sourced input is Rhin 1987 (exponent 13.3, via
>   Simons–de Weger), adopted in LEDGER L-A7 and used by `-035` and `-043`; the L-A7 thresholds
>   were recomputed there (n ≈ 2233). The "proved" ticket-mass bound of `ARBRE` is a bound on a
>   model expectation; the step from model to certainty remains open (L-A7 scope).
> - `THEOREME_SEPARATION_CONTENU.md`: "Lean : à faire" is done — `OneObstruction/ContentSeparation.lean`;
>   its paths `tests_math/` and `findings/` are `experiments/` here.
> - `run_048.py`: read its 2026-09-26 amendment, then `run_127`–`run_130`.

Independent Python verification for the shared-ledger claims (the numeric
half of Merle's key; the Lean kernel is in `../OneObstruction/`).

Each script is **canary-checked**: it must first reproduce an already-published
value before its new results are trusted. Standalone (Python 3 + `mpmath`,
`numpy`); big integers are exact — no floating point in the load-bearing checks.
Run any with `python3 test_REQ-MATH-NNN_*.py`; exit code 0 iff its canary passes.

| Script | Ledger | What it checks |
|---|---|---|
| `test_REQ-MATH-002_cf_log23_p22gap.py` | L1 | CF of log₂3; the good-`n` grid and the p=22 hole (shadow of partial quotient 23) |
| `test_REQ-MATH-005_localglobal_p22margins.py` | L1, L3 | pre-correction margins at p=21/22/23; local-global defect on p=7 (solvable over ℝ/ℤ₂/ℤ₃, never ℤ) + uniform distance |
| `test_REQ-MATH-003_staircase_p7_twokey.py` | L2 | two-key re-verification of the p=7 staircase (γ=6.7438, size 7/7, divisibility 0/7) |
| `test_REQ-MATH-006_recurrence_ghost.py` | L-A1 | the transport recurrence as an exact identity (canary + random profiles); companion to the Lean artifact |
| `test_REQ-MATH-009_transfer_spectrum.py` | L4 | independent F-map; AEH exact class values; 8-class transfer-matrix spectrum (gap ≈ 0.95) |
| `test_REQ-MATH-001_scissors_cstar.py` | context | the scissors: required exponent c\*≈0.96 < 2 (below Dirichlet's floor) |
| `test_REQ-MATH-004_scissors_race.py` | context | scissors race: k_min ~ √X₀ vs k_max ≤ X₀^⅓ — the window opens with more verification |
| `test_REQ-MATH-007_campagne_HR.py` | context | H_R campaign (62 instances; `R mod q` uniform, never 0) |
| `test_REQ-MATH-008_paralleles_ou_pas.py` | context | powers of 2 vs 3 are not parallel: minimal gap strictly decreasing → 0, never 0 |
| `test_REQ-MATH-010_kangourous_cycles_reels.py` | context | the four real cycles (1, −1, −5, −17) each anchored to a near-miss q; 256/243 carries none (771 profiles, one rotation per profile via L-A1) |
| `test_REQ-MATH-011_pourquoi_le_signe.py` | context | why the sign: the 3x−1 mirror, the shared envelope q₊+q₋=2^⌊kL⌋, the Benford log₂(3/2)=58.5% side-bias, the three Catalan free-locks (\|q\|=1), and the exhaustive k≤10 map of both signs |
| `test_REQ-MATH-012_repeated_word_law.py` | L-A2 | independent key on the repeated-word gcd law: `gcd(q_P, R_0(B^j)) = \|q_P\|/q_red(B)`, forced > 1, divisible iff the base is — 2,400 exact checks (hand-computed canaries first), conventions re-derived from this stack only |

The "context" scripts underpin the joint note's framing (the scissors, the
class spectrum, the geometry) rather than a single numbered claim.
