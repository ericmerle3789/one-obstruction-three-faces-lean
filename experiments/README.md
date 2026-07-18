# Verification scripts — Merle side

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

The "context" scripts underpin the joint note's framing (the scissors, the
class spectrum, the geometry) rather than a single numbered claim.
