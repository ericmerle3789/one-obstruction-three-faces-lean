# Re-check on a patched Lean kernel (2026-09-23)

**Why.** Lean 4 kernel soundness bug [leanprover/lean4#14576](https://github.com/leanprover/lean4/issues/14576)
("Kernel accepts wrong-structure projections, allowing an axiom-free proof of False"), filed and closed
2026-07-28, fixed in **v4.32.2** the same day. Every kernel claim in this repository was checked on
**v4.27.0** (see `../lean-toolchain`), which predates the fix. The bug's reproduction builds a declaration by
hand through `addDecl` (metaprogramming); none of the files here do anything of the kind — they are
ordinary tactic proofs, and their axiom logs show only `propext`, `Classical.choice`, `Quot.sound`. The
risk was therefore remote, but the only honest remedy is to re-run the kernel after the fix.

**What was done.** All six files recompiled from scratch in a fresh project on **Lean 4.34.0** (post-fix;
`lean_version.txt`) with **Mathlib v4.34.0** (`lake-manifest.json`), under the hardened four-check protocol:

| file | errors | stack overflow / abort | `sorryAx` | declarations in the axiom log |
|---|---|---|---|---|
| LegendreApprox | 0 | 0 | 0 | 0 (no `#print axioms`) |
| TransportRecurrence | 0 | 0 | 0 | 2 |
| ContentDescent | 0 | 0 | 0 | 5 |
| ContentSeparation | 0 | 0 | 0 | 5 |
| DeficitLemma | 0 | 0 | 0 | 10 |
| T1Structure | 0 | 0 | 0 | 18 |

**40 declarations, every one depending only on a subset of `[propext, Classical.choice, Quot.sound]`**
(`axioms_v4.34.txt`; a few now show `[propext, Quot.sound]` where v4.27.0 showed kernel-3 — Mathlib's
internals moved, not our proofs).

**What changed in the sources.** Five files are byte-identical to the published v4.27.0 files. In
`T1Structure.lean`, three lines: the import path (`import OneObstruction.LegendreApprox`, project layout),
and two Mathlib renames of 2026-09-01 — `Finset.prod_le_prod` → `Finset.prod_le_prod₀` and
`Finset.prod_lt_prod_of_nonempty` → `Finset.prod_lt_prod_of_nonempty₀`, same statements and argument
order (the old names now denote the ordered-monoid versions). No proof changed.

**Reproduce.** `cd recheck-v4.34 && lake exe cache get && lake build`.
