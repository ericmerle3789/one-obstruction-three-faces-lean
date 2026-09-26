import Mathlib
import Labo.Blueprint
import Labo.S2_Knight

/-!
# LABO-COLLATZ · S3-A · A5 Architecte (2026-09-26) — statements of the K★ path

This file contains ONLY definitions: two new objects (`ChrisSum`, `knightWord`) and one
`def <X>_enonce : Prop` per node of the path to K★ (Knight 2026, uniform form).
No proof term of any kind lives here.  Proofs go to `Labo/Tent_<node>_<agent>.lean` (PROGRAMME_S3).
Freezing is done by RT-1 (`noyau.py geler`), never here.

Conventions (from `Labo.Blueprint`, namespace `LaboBP`): a parity word is a `List Bool`,
`true` = odd step, `N = w.length`, `r = w.count true`, `C w = Σ_j 2^{p_j} 3^{r-1-j}` (in `ℕ`),
`d w = 2^N - 3^r` (in `ℤ`), `Ca a w` = the same sum with `a` in place of `3` (`S2_Knight`).

Route A (Mots, S2): B11 (Gersonides±), B7 (rotation), B14 (K-geo, via a root `t` of 2 mod `|d|`),
the plumbing `ChrisSum 3 N r = C (knightWord N r)`, then K★(c).  No Floor-shift node
(B13 is false for `r = 1`, REDTEAM_S2_RT-1 §8.3): route A does not need it.
-/

namespace LaboK

open LaboBP

/-- **ChrisSum** (S2 · architecte): `Σ_{j<r} 2^{⌊Nj/r⌋} · a^{r-1-j}`.
For `1 ≤ r ≤ N`, `a = 3`, it is `C` of the Knight (upper Christoffel) word (`chrisSum_eq_enonce`). -/
def ChrisSum (a N r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, 2 ^ (N * j / r) * a ^ (r - 1 - j)

/-- **knightWord N r**: the word of length `N` whose ones sit at positions `⌊Nj/r⌋`, `j < r`
(for `1 ≤ r ≤ N`).  Written as the concatenation of `r` blocks: block `j` is a `1` followed by
`⌊N(j+1)/r⌋ - ⌊Nj/r⌋ - 1` zeros.  Designed for induction on the number of blocks `k ≤ r`:
if `P k` is the concatenation of the first `k` blocks, then `C (P (k+1)) = 3 · C (P k) + 2^{⌊Nk/r⌋}`
(by `Ca_append`), and `|P k| = ⌊Nk/r⌋`.  Outside `1 ≤ r ≤ N` the word is not meaningful
(truncated subtraction); every statement below that uses it assumes `r ≤ N`. -/
def knightWord (N r : ℕ) : List Bool :=
  ((List.range r).map
    (fun j => true :: List.replicate (N * (j + 1) / r - N * j / r - 1) false)).flatten

/-! ## B11 — Gersonides± (Levi ben Gerson, 1343).  The only place where C1 (sign) and C3 (the prime 3)
are consumed on the K★ path. -/

/-- **B11+.** `2^N − 3^r = 1` ⇔ `(N, r) ∈ {(1, 0), (2, 1)}` (the direction used by K★). -/
def gersonides_pos_enonce : Prop :=
  ∀ N r : ℕ, (2 : ℤ) ^ N - 3 ^ r = 1 → (N = 1 ∧ r = 0) ∨ (N = 2 ∧ r = 1)

/-- **B11−.** `3^r − 2^N = 1` ⇒ `(N, r) ∈ {(1, 1), (3, 2)}` (the negative cycles −1 and −5 of C1). -/
def gersonides_neg_enonce : Prop :=
  ∀ N r : ℕ, (3 : ℤ) ^ r - 2 ^ N = 1 → (N = 1 ∧ r = 1) ∨ (N = 3 ∧ r = 2)

/-! ## B7 — rotation.  Child `rot_step` (one letter moved to the end, any multiplier `a`), then
`rot_dvd` (base 3, any number of rotations). -/

/-- **B7, one step, uniform in `a`.**  `(b :: v).rotate 1 = v ++ [b]` and
`2·C_a(v·b) = a^b·C_a(b·v) + b·(2^N − a^r)` with `N = |b·v|`, `r = #1(b·v)`. -/
def rot_step_enonce : Prop :=
  ∀ (a : ℕ) (b : Bool) (v : List Bool),
    2 * (Ca a (v ++ [b]) : ℤ) =
      (if b then (a : ℤ) else 1) * (Ca a (b :: v) : ℤ) +
        (if b then (2 : ℤ) ^ (v.length + 1) - (a : ℤ) ^ ((b :: v).count true) else 0)

/-- **B7 (base 3).**  `d(w) ∣ C(w)` ⇒ `d(w) ∣ C(ρ^k w)` (note `d (w.rotate k) = d w`). -/
def rot_dvd_enonce : Prop :=
  ∀ (w : List Bool) (k : ℕ), d w ∣ (C w : ℤ) → d w ∣ (C (w.rotate k) : ℤ)

/-! ## B14 — K-geo (route A).  Children: `kgeo_ring` (the reindexation `j ↦ Nj mod r`, in any
commutative ring, no inverse needed) and `kgeo_root` (the root `t` of 2 modulo `m = |2^N − a^r|`). -/

/-- **B14, child 1 (reindexation).**  If `t^r = 2` and `t^N = a` in a commutative ring and
`gcd(N, r) = 1`, then `ChrisSum a N r = t^{(N−1)(r−1)} · Σ_{s<r} t^s`.
(Each term is `t^{N(r−1) − (Nj mod r)}` and `j ↦ Nj mod r` permutes `range r`.) -/
def kgeo_ring_enonce : Prop :=
  ∀ (R : Type) [CommRing R] (a N r : ℕ) (t : R), Nat.Coprime N r → t ^ r = 2 → t ^ N = (a : R) →
    ((ChrisSum a N r : ℕ) : R) = t ^ ((N - 1) * (r - 1)) * ∑ s ∈ Finset.range r, t ^ s

/-- **B14, child 2 (the root of 2).**  `a` odd, `1 ≤ r ≤ N`, `gcd(N, r) = 1`: in `ℤ/m`,
`m = |2^N − a^r|`, there is `t` with `t^r = 2` and `t^N = a` (`t = 2^β a^{−γ}`, `βr = 1 + γN`). -/
def kgeo_root_enonce : Prop :=
  ∀ a N r : ℕ, Odd a → 1 ≤ r → r ≤ N → Nat.Coprime N r →
    ∃ t : ZMod ((2 : ℤ) ^ N - (a : ℤ) ^ r).natAbs, t ^ r = 2 ∧ t ^ N = (a : ZMod _)

/-- **B14 (K-geo).**  Uniform in odd `a`, both signs of `2^N − a^r`:
`a` odd, `1 ≤ r ≤ N`, `gcd(N, r) = 1` ⇒ `ChrisSum a N r` and `2^N − a^r` are coprime in `ℤ`. -/
def kgeo_enonce : Prop :=
  ∀ a N r : ℕ, Odd a → 1 ≤ r → r ≤ N → Nat.Coprime N r →
    IsCoprime (ChrisSum a N r : ℤ) ((2 : ℤ) ^ N - (a : ℤ) ^ r)

/-! ## Plumbing: `ChrisSum` is `C` of the Knight word. -/

/-- **Plumbing (a).**  `r ≤ N` ⇒ `ChrisSum 3 N r = C (knightWord N r)` (true also for `r = 0`). -/
def chrisSum_eq_enonce : Prop :=
  ∀ N r : ℕ, r ≤ N → ChrisSum 3 N r = C (knightWord N r)

/-- **Plumbing (b).**  `1 ≤ r ≤ N` ⇒ the Knight word has length `N` and `r` ones
(so `d (knightWord N r) = 2^N − 3^r`). -/
def knightWord_shape_enonce : Prop :=
  ∀ N r : ℕ, 1 ≤ r → r ≤ N → (knightWord N r).length = N ∧ (knightWord N r).count true = r

/-! ## K★(c) — Knight 2026, uniform form, at the kernel. -/

/-- **K★(c).**  If `x > 0` is the cycle point `x · d(w) = C(w)` of a rotation `w` of the Knight word
`knightWord N r`, with `gcd(N, r) = 1` and `1 ≤ r ≤ N`, then `(N, r) = (2, 1)` (the cycle {1, 2}).
`x > 0` is necessary: `(N, r) = (1, 1), x = −1` and `(3, 2), x = −5` (C1). -/
def Kstar_enonce : Prop :=
  ∀ (N r k : ℕ) (x : ℤ), Nat.Coprime N r → 1 ≤ r → r ≤ N → 0 < x →
    x * d ((knightWord N r).rotate k) = (C ((knightWord N r).rotate k) : ℤ) → N = 2 ∧ r = 1

end LaboK
