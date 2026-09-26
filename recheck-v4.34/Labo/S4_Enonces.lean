import Mathlib
import Labo.Blueprint
import Labo.S2_Pont
import Labo.S3_Enonces

/-!
# LABO-COLLATZ · S4-A · A5 Architecte (2026-09-26) — statements FEN, B18o, K★-orbit, Ck2

This file contains ONLY definitions: four new objects (`oddIdx`, `phases`, `blocks`, `Phi2`) and one
`def <X>_enonce : Prop` per node.  No proof term, no `theorem`, no `example` lives here.
Proofs go to `Labo/Tent_<node>_<agent>.lean` (PROGRAMME_S4).  Freezing is done by RT-1
(`noyau.py geler`), never here.

Conventions (from `Labo.Blueprint`, namespace `LaboBP`): `T` is the Terras map on `ℤ`
(`x % 2` is `Int.emod`, so `x % 2 ∈ {0, 1}` also for `x < 0`); a parity word is a `List Bool`,
`true` = odd step, `N = w.length`, `r = w.count true`; `pw T x n` = the first `n` parity bits of
the orbit of `x`; `Follows x w := pw T x w.length = w`; `C`, `d w = 2^N − 3^r` as in B0.

Validity (PROCEDURE_CREATION, step 0), written before any condition:
* orbit statements (`orbitProd`, `window`) need `x ≠ 0`: the orbit of `0` is `0 ↦ 0` (tomb 9),
  and at `x = 0, n = 1` the product identity reads `2 = 1`;
* phase statements need `Nat.Coprime N r`: then `j ↦ r·p_j − N·j` is injective and `phases w` is a
  transversal of `ℤ/r` (`r` elements).  Without it phases collapse (`1010`: `{0}`);
  `phases` of a rotation is a translate of `phases` (so `blocks` is a necklace invariant);
* the 2-block normal form is `[0, lam) ∪ [lam + g·r, r + g·r)` up to translation, `1 ≤ lam ≤ r − 1`,
  `g ≥ 1` (`g = 0, −1` glue the blocks; `g ≤ −2` becomes `g' = −g − 1 ≥ 1` by swapping the blocks);
  validity (L2, necessity) gives `g + 1 ≤ N / r` (RT-1 S3B §2.6: no truncated `N / r − 1`).

Proof path of `Ck2` (A4 assembly), all directions at the kernel:
`x·d = C` ⇒ `Follows x w ∧ T^[N] x = x`  (`LaboBP.B4_int`, `Labo/S2_B5.lean`: this is the direction
RT-1 S3B §2.6 asked about; `B2` alone needs `Follows`) ⇒ `N ≤ 2r` (`window` + `oddCount`), while
`k2Long` (from `k2NormalForm` + `k2ValidBound`) gives `2r + 1 ≤ N`; `x ≠ 0` comes from `C w > 0`
(`LaboBP.C_pos`, S2_B5).  Tree: `Ck2 ← {B4_int, C_pos, window, oddCount, k2Long}`,
`window ← orbitProd`, `k2Long ← {k2NormalForm, k2ValidBound}`,
`k2NormalForm ← {twoBlocks, phasesTransversal}` (optional), `k2ValidBound ← phasesSucc` (L2),
`Kstar_orbit ← {B2, length_pw/follows_pw (S2_B5), LaboK.Kstar_enonce (Kstar_thm, S3 KEEP)}`.
-/

namespace LaboF

open LaboBP

/-! ## Orbit objects -/

/-- The odd indices `i < n` of the orbit of `x` (a set of *indices*, so the products below are
indexed by the orbit: a multiset of values, never a set of values). -/
def oddIdx (x : ℤ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => (T^[i] x) % 2 = 1)

/-! ## Phase objects (Mots, S2–S3; L1–L3) -/

/-- **Phases** of a word: `{r·p_j − N·j}` where `p_j` is the position of the `j`-th `1`
(`j = #1` strictly before `p_j`).  With `gcd(N, r) = 1` this is a transversal of `ℤ/r`. -/
def phases (w : List Bool) : Finset ℤ :=
  ((Finset.range w.length).filter (fun i => w.getD i false = true)).image
    (fun (i : ℕ) => (w.count true : ℤ) * (i : ℤ) - (w.length : ℤ) * ((w.take i).count true : ℤ))

/-- **Blocks** of a finite set of integers: the number of maximal runs of consecutive integers
(= number of `x ∈ S` with `x − 1 ∉ S`). -/
def blocks (S : Finset ℤ) : ℕ :=
  (S.filter (fun x => x - 1 ∉ S)).card

/-- **The 2-block normal form** `[0, lam) ∪ [lam + g·r, r + g·r)` (L3, Mots). -/
def Phi2 (g lam r : ℕ) : Finset ℤ :=
  Finset.Ico (0 : ℤ) (lam : ℤ) ∪ Finset.Ico ((lam : ℤ) + (g : ℤ) * (r : ℤ)) ((r : ℤ) + (g : ℤ) * (r : ℤ))

/-! ## (1) B18o — the product identity, indexed by the orbit -/

/-- **B18o.**  A nonzero `n`-periodic point of `T`:
`2^n · ∏_{i < n, x_i odd} x_i = ∏_{i < n, x_i odd} (3 x_i + 1)`, `x_i = T^[i] x`.
`x ≠ 0` is necessary (`x = 0, n = 1`: `2 = 1`). -/
def orbitProd_enonce : Prop :=
  ∀ (x : ℤ) (n : ℕ), x ≠ 0 → T^[n] x = x →
    2 ^ n * ∏ i ∈ oddIdx x n, T^[i] x = ∏ i ∈ oddIdx x n, (3 * T^[i] x + 1)

/-- **Plumbing.**  The number of `true` in the parity word is the number of odd indices. -/
def oddCount_enonce : Prop :=
  ∀ (x : ℤ) (n : ℕ), (pw T x n).count true = (oddIdx x n).card

/-! ## (2) FEN — the window, sign-blind -/

/-- **FEN.**  A nonzero `n`-periodic point of `T` (`n ≥ 1`) has `n ≤ 2r`, `r = #odd indices`,
and `n = 2r` only on the cycle `{1, 2}`.  (From `|3y+1| ≤ 4|y|`, equality iff `y = 1`.)
`x ≠ 0` is necessary (`x = 0`: `r = 0`). -/
def window_enonce : Prop :=
  ∀ (x : ℤ) (n : ℕ), x ≠ 0 → 0 < n → T^[n] x = x →
    n ≤ 2 * (oddIdx x n).card ∧ (n = 2 * (oddIdx x n).card → x = 1 ∨ x = 2)

/-! ## (3) K★ in orbit form -/

/-- **K★-orbit.**  A positive `n`-periodic point of `T` whose parity word (with `r` ones,
`gcd(n, r) = 1`) is a rotation of the Knight word `knightWord n r` is `1` or `2`.
`r` is *defined* as the number of ones of the parity word (hypothesis `hr`, a definition, not a
restriction); `1 ≤ r ≤ n` is derivable.  `0 < x` is necessary (C1: `x = −1`, `n = r = 1`). -/
def Kstar_orbit_enonce : Prop :=
  ∀ (x : ℤ) (n r k : ℕ), 0 < x → 0 < n → T^[n] x = x →
    (pw T x n).count true = r → Nat.Coprime n r →
    pw T x n = (LaboK.knightWord n r).rotate k → x = 1 ∨ x = 2

/-! ## (4) Blocks and Ck2 -/

/-- **Infrastructure (L1, pure combinatorics of `Finset ℤ`).**  A finite set of integers with two
blocks is the union of two maximal intervals `[a, a + l) ∪ [b, b + m)`, `l, m ≥ 1`, `a + l < b`.
(Optional child of `k2NormalForm`; reusable for k = 3.) -/
def twoBlocks_enonce : Prop :=
  ∀ S : Finset ℤ, blocks S = 2 →
    ∃ (a b : ℤ) (l m : ℕ), 1 ≤ l ∧ 1 ≤ m ∧ a + (l : ℤ) < b ∧
      S = Finset.Ico a (a + (l : ℤ)) ∪ Finset.Ico b (b + (m : ℤ))

/-- **Infrastructure (transversal).**  `gcd(N, r) = 1` ⇒ `phases w` has `r` elements, pairwise
incongruent modulo `r`.  (Optional child of `k2NormalForm`.) -/
def phasesTransversal_enonce : Prop :=
  ∀ w : List Bool, Nat.Coprime w.length (w.count true) →
    (phases w).card = w.count true ∧
      ∀ y ∈ phases w, ∀ z ∈ phases w, y ≡ z [ZMOD (w.count true : ℤ)] → y = z

/-- **L2 (validity, necessity).**  Every phase `y` has a successor phase `z ≡ y − N (mod r)` with
`y − z ≤ N − r` (the gap between consecutive ones is `≥ 1`; the last one wraps to the first).
No coprimality needed.  (Child of `k2ValidBound`; reusable for k = 3.) -/
def phasesSucc_enonce : Prop :=
  ∀ w : List Bool, ∀ y ∈ phases w, ∃ z ∈ phases w,
    z ≡ y - (w.length : ℤ) [ZMOD (w.count true : ℤ)] ∧
      y - z ≤ (w.length : ℤ) - (w.count true : ℤ)

/-- **k2NormalForm (L3, form).**  `gcd(N, r) = 1` and two blocks of phases ⇒ the phases are a
translate of `Phi2 g lam r` with `g ≥ 1`, `1 ≤ lam < r`. -/
def k2NormalForm_enonce : Prop :=
  ∀ w : List Bool, Nat.Coprime w.length (w.count true) → blocks (phases w) = 2 →
    ∃ (s : ℤ) (g lam : ℕ), 1 ≤ g ∧ 1 ≤ lam ∧ lam < w.count true ∧
      phases w = (Phi2 g lam (w.count true)).image (fun y => y + s)

/-- **k2ValidBound (L3, validity bound; L2 necessity).**  If the phases of a word are a translate
of `Phi2 g lam r` (`g ≥ 1`, `1 ≤ lam < r`, `gcd(N, r) = 1`) then `g + 1 ≤ N / r`. -/
def k2ValidBound_enonce : Prop :=
  ∀ (w : List Bool) (s : ℤ) (g lam : ℕ), Nat.Coprime w.length (w.count true) →
    1 ≤ g → 1 ≤ lam → lam < w.count true →
    phases w = (Phi2 g lam (w.count true)).image (fun y => y + s) →
    g + 1 ≤ w.length / w.count true

/-- **k2Long (L3, corollary).**  `gcd(N, r) = 1` and two blocks of phases ⇒ `2r + 1 ≤ N`. -/
def k2Long_enonce : Prop :=
  ∀ w : List Bool, Nat.Coprime w.length (w.count true) → blocks (phases w) = 2 →
    2 * w.count true + 1 ≤ w.length

/-- **Ck2 (ex-conjecture C-k2).**  `a = 3`, `gcd(N, r) = 1`, two blocks of phases ⇒ no integer
`x` with `x·d(w) = C(w)`.  No `|d| > 1`, no sign, no primitivity.  False for `a = 5`
(`11000`: `C_5 = 7 = 1·(2^5 − 5^2)`). -/
def Ck2_enonce : Prop :=
  ∀ w : List Bool, Nat.Coprime w.length (w.count true) → blocks (phases w) = 2 →
    ∀ x : ℤ, x * d w ≠ (C w : ℤ)

end LaboF
