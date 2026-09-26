# `Labo/` — kernel results of Merle's lab since round 16 (offered for information)

**Status.** Offered in round 17 (§3) for information only: no ledger entry, no new mathematics claimed.
Written with an AI collaborator under the lab's protocol (statements frozen under two keys before any proof;
an oracle judges each proof; a separate Lean referee re-checks cold). Namespaces `LaboBP`, `LaboK`, `LaboF`.

**Toolchain.** Lean **4.34.0** (post lean4#14576) + Mathlib **v4.34.0** — the same project as `RECHECK.md`
(`lean-toolchain`, `lake-manifest.json` unchanged; `lakefile.toml` gains a `[[lean_lib]] name = "Labo"` block).

**Build.** One module at a time — there is no `Labo.lean` root, so `lake build Labo` is not a target:

```
cd recheck-v4.34
lake exe cache get
lake build Labo.S2_B5 Labo.S4_K_window Labo.Tent_Kstar_orbit_formaliste Labo.Tent_Ck2_formaliste
```

These four targets build all 21 files. Expected: 0 errors; one warning `declaration uses 'sorry'` at
`Blueprint.lean:93` (see below); linter and deprecation warnings only otherwise.

**The one `sorry`.** `Blueprint.lean` states the open target T★ and marks it `theorem Tstar_open : Tstar :=
by sorry`. Nothing imports it as a proof; every theorem below depends only on
`[propext, Classical.choice, Quot.sound]` (or a subset).

**Cold re-check by the lab's Lean referee (RT-2), 2026-09-26.** All 21 files recompiled into a fresh olean
directory with the workshop's build cache removed from `LEAN_PATH`, Mathlib oleans reused; axioms read by
`Lean.collectAxioms` on every constant of every module (auxiliaries included) and by `#print axioms` on the
theorem heads: standard axioms only, no `sorryAx` outside `Tstar_open`, no `_native`/`ofReduceBool`/
`trustCompiler`, no `axiom` declaration; frozen statements printed identical to their frozen text.
Same kernel as the workshop: a bug of the kernel itself is not excluded by this check. The files here are
byte-identical copies of the re-checked ones (sha256 prefixes listed at the end of this file). This directory's own
layout was then rebuilt once from scratch (2026-09-26, the four targets above, Mathlib oleans reused):
21 modules, 0 errors, the single `sorry` warning above, and `#print axioms` of `B2`, `B4_int`, `B5`,
`window_thm`, `Kstar_orbit_thm`, `Ck2_thm` = `[propext, Classical.choice, Quot.sound]`.

## What each file proves

Conventions: `T x = x/2` (even) or `(3x+1)/2` (odd) on `ℤ`; a parity word is a `List Bool`, `true` = odd,
`N = length`, `r = #true`; `d(w) = 2^N − 3^r`; `C(w) = Σⱼ 2^{pⱼ}·3^{r−1−j}` (`pⱼ` = position of the `j`-th one);
`Follows x w` = the first `N` parity bits of the orbit of `x` are `w`.

| file | content |
|---|---|
| `Blueprint.lean` | definitions (`T`, `Tp`, `pw`, `C`, `Csum`, `d`, `Follows`, `Tstar`) and the statements `B1`–`B5`; the marker `Tstar_open` |
| `S2_Pont.lean` | **the bridge**: `B1` (`Follows x w → 2^N·T^N x = 3^r·x + C(w)`), `B2` (`Follows x w → (T^N x = x ↔ x·d(w) = C(w))`), `B3` (positive cycle ⇒ `d > 0`), `C = Csum`; small `decide` witnesses (cycles `−1`, `−5`, `−17`; `5x+1`; `3x+5`) |
| `S2_Bits.lean` | parity-bit bijection for every odd `p`: same first `k` bits ⇔ `x ≡ y (mod 2^k)`; every bit pattern occurs (Terras 1976 / Lagarias 1985) |
| `S2_B5.lean` | `B4_int`: an integer solution of `x·d(w) = C(w)` follows `w` and is an `N`-cycle; `C_pos`; `B5`: T★ ⇔ every positive cycle is `{1, 2}` |
| `S2_Knight.lean` | the swap identity `C_a(u01) − C_a(u10) = 2^{|u|}` for every multiplier `a`, and its consequence: `d` dividing both forces `d = ±1` |
| `S3_Enonces.lean` | statements of the K★ path (`LaboK`): Knight word, `ChrisSum`, Gersonides±, rotation, K-geo, `Kstar_enonce` |
| `S3_K_rot_dvd.lean` | `d(w) ∣ C(w)` ⇒ `d(w) ∣ C(w.rotate k)` |
| `S3_K_kgeo.lean` | `a` odd, `1 ≤ r ≤ N`, `gcd(N, r) = 1` ⇒ `ChrisSum a N r` and `2^N − a^r` are coprime (both signs) |
| `S3_K_chrisSum_eq.lean` | `ChrisSum 3 N r = C(knightWord N r)` |
| `S3_K_knightWord_shape.lean` | the Knight word has length `N` and `r` ones |
| `S3_K_gersonides_pos.lean` | `2^N − 3^r = 1` ⇒ `(N, r) ∈ {(1, 0), (2, 1)}` (Levi ben Gerson) |
| `Tent_Kstar_formaliste.lean` | **K★ (cycle-equation form)**: `gcd(N, r) = 1`, `1 ≤ r ≤ N`, `x > 0`, `x·d(w) = C(w)` for a rotation `w` of the Knight word ⇒ `(N, r) = (2, 1)`; route: rotation invariance + K-geo + Gersonides, not Knight's reversal symmetry |
| `S4_Enonces.lean` | statements `LaboF`: `oddIdx`, `phases` (`{r·pⱼ − N·j}`), `blocks` (runs of consecutive integers), `Phi2`; FEN, B18o, K★-orbit, the block lemmas, `Ck2` |
| `S4_K_orbitProd.lean` | B18o: for a nonzero `n`-periodic `x`, `2^n·∏ x_i = ∏ (3x_i + 1)` over the odd indices of the orbit |
| `S4_K_oddCount.lean` | the number of ones of the parity word is the number of odd indices |
| `S4_K_window.lean` | **FEN**: nonzero `n`-periodic `x` (`n ≥ 1`) ⇒ `n ≤ 2r`, and `n = 2r` ⇒ `x ∈ {1, 2}` — both signs (classical for `x > 0`: Eliahou 1993, Thm 2.1) |
| `S4_K_k2NormalForm.lean` | `gcd(N, r) = 1`, two blocks of phases ⇒ phases are a translate of `Phi2 g lam r`, `g ≥ 1` |
| `S4_K_k2ValidBound.lean` | that normal form forces `g + 1 ≤ N / r` |
| `Tent_k2Long_formaliste.lean` | `gcd(N, r) = 1`, two blocks ⇒ `2r + 1 ≤ N` |
| `Tent_Ck2_formaliste.lean` | **Ck2**: `gcd(N, r) = 1`, two blocks ⇒ `∀ x : ℤ, x·d(w) ≠ C(w)` (FEN against `k2Long`; false for `5x+1`, word `11000`) |
| `Tent_Kstar_orbit_formaliste.lean` | **K★ in orbit form**: `x > 0`, `T^n x = x`, parity word a rotation of `knightWord n r`, `gcd(n, r) = 1` ⇒ `x ∈ {1, 2}` |

**Prior formalisation.** Knight's theorem was formalised earlier by another author:
`github.com/tcosmo/Knight2026_lean` (Lean 4.28, main theorem in the form of Knight's Thm 5.4). It was not
re-run here. The versions above differ only in form (whole rotation class, `x > 0` rather than `d > 0`,
`r = 1` included); the `gcd(n, r) > 1` case is not covered.

**What these do not exclude.** K★ sees only rotations of the Knight word with `gcd(n, r) = 1`; Ck2 is a
consequence of FEN and excludes nothing with three or more blocks; FEN is sign-blind and excludes no cycle
with `N < 2r`. `−17` (five blocks, `N = 11 < 2r = 14`) is untouched by all of them.

## sha256 prefixes of the files (2026-09-26)

| file | sha256[:16] |
|---|---|
| `Labo/Blueprint.lean` | `c397d06ecff99312` |
| `Labo/S2_B5.lean` | `0683a0a1d2f79a2e` |
| `Labo/S2_Bits.lean` | `3115c21468678843` |
| `Labo/S2_Knight.lean` | `8e430e3a1fbcaf63` |
| `Labo/S2_Pont.lean` | `a7ea2ed74d1e3f58` |
| `Labo/S3_Enonces.lean` | `7aece8771ab3d1fb` |
| `Labo/S3_K_chrisSum_eq.lean` | `924525944a22d32b` |
| `Labo/S3_K_gersonides_pos.lean` | `52bd33396eda2e94` |
| `Labo/S3_K_kgeo.lean` | `e7e2b855fe5bb232` |
| `Labo/S3_K_knightWord_shape.lean` | `066cf10bf71ce1e1` |
| `Labo/S3_K_rot_dvd.lean` | `15fab505284b983d` |
| `Labo/S4_Enonces.lean` | `879e2827703f8778` |
| `Labo/S4_K_k2NormalForm.lean` | `119aed96a019ca97` |
| `Labo/S4_K_k2ValidBound.lean` | `320fd60c08e65116` |
| `Labo/S4_K_oddCount.lean` | `687730adcb960f03` |
| `Labo/S4_K_orbitProd.lean` | `dda46544bf18954d` |
| `Labo/S4_K_window.lean` | `5b616a1c7b155db6` |
| `Labo/Tent_Ck2_formaliste.lean` | `12e0a0b49f94a99c` |
| `Labo/Tent_Kstar_formaliste.lean` | `cc02122b86a88ae7` |
| `Labo/Tent_Kstar_orbit_formaliste.lean` | `2603c98c5ffc58f3` |
| `Labo/Tent_k2Long_formaliste.lean` | `217827087494791e` |
