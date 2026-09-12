# Naming note — `run_050.py` in this repository (2026-09-12)

`experiments/run_050.py` here is the **round-14 exact witness for `LEDGER.md` L-A10** (the
ascending fixed point, `r_p = −(p−2)^{−1} mod 2^{k+1}`), committed at `db0e89d` and cited under
that name by the shared ledger and by Macindoe's review. **Its public name does not change.**

In the Merle research journal, however, the label BRECHE-050 (§97, 2026-08-01) belongs to a
*different* script — the polynomial rank-function refutation. On 2026-09-03 the round-14 witness
was written locally under the name `run_050.py` and **overwrote that original**. The original
was recovered on 2026-09-12 from the session transcript and restored (its re-run is
byte-identical to the archived `OUT_BRECHE-050.txt`); the witness now lives locally as
`run_050b.py`. No mathematical content changed on either side. Recorded so that a reader
cross-referencing the journal and this repository is not misled by the shared number.
