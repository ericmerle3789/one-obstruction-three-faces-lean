# One Obstruction, Three Faces — Merle Lean stack

The **Lean 4 verification stack** (Eric Merle's "kernel key") for the joint note
*One obstruction, three faces* with Benjamin Macindoe.

Per the collaboration protocol's three-repo model, each side's verification
stack lives in its own repository and is never merged into the other's:

- **this repo** — Merle side, the Lean kernel key;
- [`macindoe/collatz`](https://github.com/macindoe/collatz) — Macindoe side, independent code;
- the shared repo (note text + protocol + claims ledger) links to both.

A load-bearing claim turns **both** keys — the Lean kernel here, independent
code there — with neither derived from the other.

## Ledger entry L-A1 — the transport recurrence

`OneObstruction/TransportRecurrence.lean`.

Independent simultaneous discovery (Merle, integer form; Macindoe, fixed-point
form, `reverse.md` 14.15.9.2), joined by the seam identity `N_r + q = 2^{m_r} R_r`.

**Certified here (kernel, 0 `sorry`, no user axioms):** from the transport
recurrence

```
2^{σ_r} · R_{r+1} = 3^{m_r} · R_r + (2^{s_r} − 1) · q ,   q = 2^K − 3^n
```

the `p` per-rotation divisibility conditions of a period-`p` cycle **collapse
to a single condition**: `q ∣ R_r ↔ q ∣ R_0` for every rotation `r`
(`transport_collapse`), equivalently `(∀ r, q ∣ R_r) ↔ q ∣ R_0`
(`cycle_divisibility_one_check`).

The modulus is the **unreduced** `q = 2^K − 3^n` (it differs from the reduced
denominator exactly when `gcd(q, R_r) > 1`, e.g. the `p = 7` seed `n = 94` has
`gcd = 7`); unit transport mod the unreduced `q` implies it mod every divisor.

**Scope, stated honestly (ARES).** The recurrence itself — the algebraic
identity that the elimination numerators `R_r` satisfy it — is *not* proved
here; it is verified numerically on both sides (29,211 checks + 60 shared
test-vectors at `macindoe/collatz`, `experiments/transport_recurrence_vectors.json`,
0 failures) and proved in fixed-point form in Macindoe `reverse.md` 14.15.9.2.
This artifact certifies the *kernel-friendly core*: recurrence ⟹ collapse. A
sanity canary (the trivial cycle, `q = 2^4 − 3^2 = 7`) is proved inside Lean to
witness that the hypothesis is non-vacuous.

## Reproduce

Verified under **Lean 4.27.0 / Mathlib v4.27.0** (rev `a3a10db`):

```
lake exe cache get     # fetch prebuilt Mathlib oleans
lake build             # builds OneObstruction; 0 errors, 0 sorry
```

or, against any Lean 4.27.0 + Mathlib project:

```
lake env lean OneObstruction/TransportRecurrence.lean
```

The file ends with `#print axioms`, whose output is the **kernel-3** profile —
no user axioms, no `native_decide`:

```
'CollatzTransport.transport_collapse' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'CollatzTransport.cycle_divisibility_one_check' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## Working conditions, disclosed

Research direction and standards of evidence are the author's; the mathematical
development is carried out with an AI collaborator (Claude) under the A.R.E.S.
protocol (independent second key, zero bibliographic recall, every assertion
traceable to a runnable check), and the Lean kernel is the final arbiter — a
model cannot bluff a compiler.

License: CC BY 4.0.
