import Mathlib

/-!
# LABO-COLLATZ · BLUEPRINT (S2, A4 Formaliste, 2026-09-26)

Definitions (node B0) and *statements* of the seed nodes of `LABO-COLLATZ/BLUEPRINT.md`.
Statements are written as `Prop`-valued definitions (`B1_statement`, …), so that this file needs
no `sorry` for them; proofs live in `Labo/S2_Pont.lean`.  The only `sorry` of this file is the
open target `Tstar_open` (T★), kept as a marker.  Nothing downstream may use it.

Conventions.  A parity word is a `List Bool`, `true` = odd step.  The first letter is the parity
of the starting point.  `r w = w.count true`, `N = w.length`.
-/

namespace LaboBP

/-- B0. Terras map on `ℤ`: `x/2` if `x` even, `(3x+1)/2` if `x` odd. -/
def T (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- B0 (cousins). `x ↦ x/2 | (p x + 1)/2`. `Tp 3 = T`; `Tp 5` is the 5x+1 cousin C3. -/
def Tp (p : ℤ) (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (p * x + 1) / 2

/-- C3 cousin: the 5x+1 map. -/
def T5 : ℤ → ℤ := Tp 5

/-- B0. First `n` parity bits of the orbit of `x` under `f` (`true` = odd). -/
def pw (f : ℤ → ℤ) (x : ℤ) : ℕ → List Bool
  | 0 => []
  | n + 1 => (x % 2 == 1) :: pw f (f x) n

/-- B0. `C [] = 0`, `C (b :: w) = [b]·3^{r(w)} + 2·C w`; equals `Σ_j 2^{p_j} 3^{r-1-j}`
(`C_eq_Csum`, proved in `S2_Pont`). -/
def C : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 3 ^ (w.count true) else 0) + 2 * C w

/-- The closed formula `Σ_{i < N, w_i = 1} 2^i · 3^{#ones strictly after i}` (= `Σ_j 2^{p_j} 3^{r-1-j}`). -/
def Csum (w : List Bool) : ℕ :=
  ∑ i ∈ Finset.range w.length,
    if w.getD i false then 2 ^ i * 3 ^ ((w.drop (i + 1)).count true) else 0

/-- B0. `d(w) = 2^N − 3^r`. -/
def d (w : List Bool) : ℤ := 2 ^ w.length - 3 ^ (w.count true)

/-- B0. The orbit of `x` under `T` has parity word `w` (first `|w|` steps). -/
def Follows (x : ℤ) (w : List Bool) : Prop := pw T x w.length = w

instance (x : ℤ) (w : List Bool) : Decidable (Follows x w) :=
  inferInstanceAs (Decidable (pw T x w.length = w))

/-- `C` = closed formula. -/
def C_eq_Csum_statement : Prop := ∀ w : List Bool, C w = Csum w

/-- **B1 (bridge).** `Follows x w → 2^N · T^N(x) = 3^r · x + C(w)`. -/
def B1_statement : Prop :=
  ∀ (x : ℤ) (w : List Bool), Follows x w →
    2 ^ w.length * T^[w.length] x = 3 ^ (w.count true) * x + (C w : ℤ)

/-- **B2 (cycle equation).** `Follows x w → (T^N(x) = x ↔ x · d(w) = C(w))`. -/
def B2_statement : Prop :=
  ∀ (x : ℤ) (w : List Bool), Follows x w → (T^[w.length] x = x ↔ x * d w = (C w : ℤ))

/-- **B3.** A positive cycle has `d(w) > 0`, i.e. `2^N > 3^r`. -/
def B3_statement : Prop :=
  ∀ (x : ℤ) (w : List Bool), 0 < x → Follows x w → w ≠ [] → T^[w.length] x = x → 0 < d w

/-- The trivial words: rotations of `(10)^k`. -/
def TrivialWord (w : List Bool) : Prop :=
  ∃ k n : ℕ, w = (List.replicate k [true, false]).flatten.rotate n

/-- **T★ (open target).**  `d(w) > 0`, `w` has at least one `1`, `d(w) ∣ C(w)` ⇒ `w` trivial.
NB: the hypothesis `true ∈ w` is necessary: `w = [false]` has `d = 1 > 0`, `C = 0`, and is the
cycle `0 ↦ 0` (see `Tstar_needs_one_witness` in `S2_Pont`). -/
def Tstar : Prop :=
  ∀ w : List Bool, 0 < d w → true ∈ w → d w ∣ (C w : ℤ) → TrivialWord w

/-- Every positive cycle of `T` lies in `{1, 2}`. -/
def PositiveCyclesTrivial : Prop :=
  ∀ x : ℤ, 0 < x → ∀ n : ℕ, 0 < n → T^[n] x = x → x = 1 ∨ x = 2

/-- **B5.** `T★ ↔` every positive cycle of `T` is `{1, 2}`. -/
def B5_statement : Prop := Tstar ↔ PositiveCyclesTrivial

/-- Parity-bit bijection (A2, S1; core of B4), for any odd `p`: same first `k` bits ⇔ `x ≡ y (2^k)`. -/
def ParityBits_statement : Prop :=
  ∀ p : ℤ, Odd p → ∀ (k : ℕ) (x y : ℤ), pw (Tp p) x k = pw (Tp p) y k ↔ (2 : ℤ) ^ k ∣ x - y

/-- Every bit pattern occurs (surjectivity half). -/
def ParityBitsSurj_statement : Prop :=
  ∀ p : ℤ, Odd p → ∀ w : List Bool, ∃ x : ℤ, pw (Tp p) x w.length = w

/-- T★ is OPEN.  Marker only: `sorry`, never to be used downstream. -/
theorem Tstar_open : Tstar := by sorry

end LaboBP
