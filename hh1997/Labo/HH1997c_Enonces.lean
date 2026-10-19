import Mathlib
import Labo.HH1997_Enonces
import Labo.HH1997b_Enonces

/-!
# LABO-COLLATZ · HH1997c · formaliste (2026-10-19) — FROZEN STATEMENTS (third batch)

L. Halbeisen, N. Hungerbühler, *Optimal bounds for the length of rational Collatz cycles*,
Acta Arith. 78 (1997) 227–239 (read at source: `LABO-COLLATZ/calculs/bibliothecaire/s6src/hh1997.pdf`, pp. 228–237).
Third batch, the estimates of `M_{l,n}`: Proposition 1, Proposition 2, Lemma 6, Remark 1, the clause of Lemma 1
"cycles are either positive or negative", and the numerical example of §4.4 (reduced to a named finite check).
Crandall (Lemma 8, Th. 1) and Eliahou (Th. 2, 3) are in the sibling batch `HH1997d`.

This file contains ONLY definitions and `def <X> : Prop` statements.  Proofs: `Labo/HH1997c_Preuves.lean`.
Builds on the frozen batches `HH1997_Enonces` (sha256 f168e123…) and `HH1997b_Enonces` (sha256 072bdf35…), not
modified; reuses `phi`, `collatzQ`, `M`, `cl`, `stilde`, `nOf` (`n(l) = ⌊l log₃ 2⌋`), `Q4`, `Lm`, `cycle`, `LaboBP.d`.

## Line-by-line comparison with the paper (statements frozen BEFORE any proof)

| paper | Lean | deviation |
|---|---|---|
| Lemma 1, last sentence: "Cycles are either positive or negative." | `lemma1_sign` | `x₀ ≠ 0` added: `{0}` is a Collatz cycle (`zero_cycle`) that is neither |
| Prop. 1: for all `l` and `n ≤ n(l)`, `M_{l,n}/(2^l − 3^n) ≤ (n/l)·1/(2 − 3^{n/l})` | `prop1` | none (at `l = 0` both sides are `0` in Lean) |
| Prop. 2: `x = 2^l/3^n`, `m = 2n − l`, `n = n(l)`, `l > 6`: `M_{l,n}/3^n ≤ α₁x^{1−1/m} + α₂(x^{1−1/m} − 1)/(x^{1/m} − 1)`, `α₁ = (2n+3l)/(9m)`, `α₂ = (6n+l)/(27m)` | `xP`, `mR`, `alpha1`, `alpha2`, `prop2` | `m` taken in ℝ (no truncation); `0 < m` is part of the statement |
| proof of Prop. 2: "if `l ≥ 160`, `s̃` is composed of `110` and `11010`" | `blocks160` | none; `blocks23` (from `l ≥ 23`) is stronger (labtrace id=447: the decomposition fails exactly for `l ∈ {1,2,3,4,6,7,9,11,12,14,17,19,22}` up to 3000) |
| Lemma 6: for all `x ∈ ]1,3[`, `l > 160`, `α = 0.9`: `f(x) = (α₁x^{1−1/m} + α₂(x^{1−1/m} − 1)/(x^{1/m} − 1))·3(x^{1/n} − 1)/(x − 1) ≤ α` | `f6`, `lemma6` | none |
| Remark 1: for all `l`, `n = n(l)`: `1/20 ≤ M_{l,n}/(n3^n) ≤ 7/10` | `remark1` | `l ≥ 2` made explicit (`n(1) = 0`: the quotient is `0/0`); `remark1_lower6` (`1/6` instead of `1/20`) is stronger |
| Remark 1: for `l > 10³`, `7/10` can be replaced by `1/2` | `remark1_large` | none |
| §4.4 example: if (C) holds for all `x₀ ≤ m = 212 366 032 807 211`, every non-trivial cycle in ℕ has length `≥ 102 225 496` | `VerifiedUpTo`, `example44` | the hypothesis is the named `VerifiedUpTo B` (never an axiom); "non-trivial" = not containing `1` |
| the finite check behind the example (Steps 1–4 of §4.4): `M_{l,n(l)}/(2^l − 3^{n(l)}) < m` for `1 ≤ l < 102 225 496` | `example44_check` | stated, as the paper's own reduction (Fourth step), with `Q4` |
| the reduction: Th. 4 + `example44_check` ⇒ `example44` | `example44_reduction` | none |
-/

namespace LaboHH

open LaboBP

/-! ## Lemma 1, last sentence -/

/-- `{0}` is a Collatz cycle in `ℚ_(2)`. -/
def zero_cycle : Prop := collatzQ 0 = 0

/-- "Cycles are either positive or negative" (for a cycle `≠ {0}`). -/
def lemma1_sign : Prop :=
  ∀ x₀ : ℚ, Odd x₀.den → x₀ ∈ Function.periodicPts collatzQ → x₀ ≠ 0 →
    (∀ y ∈ cycle x₀, 0 < y) ∨ (∀ y ∈ cycle x₀, y < 0)

/-! ## Proposition 1 -/

/-- Prop. 1. -/
def prop1 : Prop :=
  ∀ l n : ℕ, n ≤ nOf l →
    (M l n : ℝ) / ((2 : ℝ) ^ l - 3 ^ n) ≤ (n : ℝ) / l * (1 / (2 - (3 : ℝ) ^ ((n : ℝ) / l)))

/-! ## Proposition 2 -/

/-- `x = 2^l / 3^{n(l)}`. -/
noncomputable def xP (l : ℕ) : ℝ := (2 : ℝ) ^ l / 3 ^ nOf l

/-- `m = 2n − l`, `n = n(l)` (in ℝ). -/
noncomputable def mR (l : ℕ) : ℝ := 2 * (nOf l : ℝ) - l

/-- `α₁ = (2n + 3l)/(9m)`. -/
noncomputable def alpha1 (l : ℕ) : ℝ := (2 * (nOf l : ℝ) + 3 * l) / (9 * mR l)

/-- `α₂ = (6n + l)/(27m)`. -/
noncomputable def alpha2 (l : ℕ) : ℝ := (6 * (nOf l : ℝ) + l) / (27 * mR l)

/-- Prop. 2. -/
def prop2 : Prop :=
  ∀ l : ℕ, 6 < l →
    0 < mR l ∧
    (M l (nOf l) : ℝ) / 3 ^ nOf l
      ≤ alpha1 l * xP l ^ (1 - 1 / mR l) + alpha2 l * (xP l ^ (1 - 1 / mR l) - 1) / (xP l ^ (1 / mR l) - 1)

/-- The 0-1 words `Z = 110` and `A = 11010`. -/
def blockZ : List Bool := [true, true, false]
def blockA : List Bool := [true, true, false, true, false]

/-- Proof of Prop. 2: for `l ≥ 160`, `s̃(l, n(l))` is a concatenation of `Z = 110` and `A = 11010`. -/
def blocks160 : Prop :=
  ∀ l : ℕ, 160 ≤ l → ∃ bs : List Bool, stilde l (nOf l) = bs.flatMap fun b => if b then blockA else blockZ

/-- The same from `l ≥ 23` (stronger than printed). -/
def blocks23 : Prop :=
  ∀ l : ℕ, 23 ≤ l → ∃ bs : List Bool, stilde l (nOf l) = bs.flatMap fun b => if b then blockA else blockZ

/-! ## Lemma 6 -/

/-- `f(x)` of Lemma 6 (with `α₁, α₂, m, n` of Prop. 2 at `l`). -/
noncomputable def f6 (l : ℕ) (x : ℝ) : ℝ :=
  (alpha1 l * x ^ (1 - 1 / mR l) + alpha2 l * (x ^ (1 - 1 / mR l) - 1) / (x ^ (1 / mR l) - 1))
    * (3 * (x ^ (1 / (nOf l : ℝ)) - 1) / (x - 1))

/-- Lemma 6 (`α = 0.9`). -/
def lemma6 : Prop := ∀ x : ℝ, 1 < x → x < 3 → ∀ l : ℕ, 160 < l → f6 l x ≤ 9 / 10

/-! ## Remark 1 -/

/-- Remark 1: `1/20 ≤ M_{l,n}/(n 3^n) ≤ 7/10`, `n = n(l)`. -/
def remark1 : Prop :=
  ∀ l : ℕ, 2 ≤ l →
    (1 / 20 : ℝ) ≤ (M l (nOf l) : ℝ) / (nOf l * 3 ^ nOf l) ∧
    (M l (nOf l) : ℝ) / (nOf l * 3 ^ nOf l) ≤ 7 / 10

/-- Remark 1, lower bound `1/6` instead of `1/20` (stronger than printed). -/
def remark1_lower6 : Prop :=
  ∀ l : ℕ, 2 ≤ l → (1 / 6 : ℝ) ≤ (M l (nOf l) : ℝ) / (nOf l * 3 ^ nOf l)

/-- Remark 1: for `l > 10³`, `7/10` can be replaced by `1/2`. -/
def remark1_large : Prop :=
  ∀ l : ℕ, 1000 < l → (M l (nOf l) : ℝ) / (nOf l * 3 ^ nOf l) ≤ 1 / 2

/-! ## The numerical example of §4.4 -/

/-- (C) verified up to `B`: every `x₀ ∈ {1, …, B}` reaches `1` under the Terras map `T`. -/
def VerifiedUpTo (B : ℕ) : Prop := ∀ x : ℕ, 1 ≤ x → x ≤ B → ∃ k : ℕ, T^[k] (x : ℤ) = 1

/-- The example: if (C) is verified up to `212 366 032 807 211`, every cycle in ℕ not containing `1` has length
`≥ 102 225 496`.  A cycle in ℕ: `x₀ ≥ 1` with `T^[p] x₀ = x₀`, `p ≥ 1`; its length is its minimal period. -/
def example44 : Prop :=
  VerifiedUpTo 212366032807211 →
    ∀ x₀ : ℕ, 1 ≤ x₀ → (x₀ : ℤ) ∈ Function.periodicPts T →
      (∀ k, T^[k] (x₀ : ℤ) ≠ 1) → 102225496 ≤ Function.minimalPeriod T (x₀ : ℤ)

/-- The finite check behind the example (Fourth step of §4.4): `M_{l,n(l)}/(2^l − 3^{n(l)}) < m` for
`1 ≤ l < 102 225 496`, i.e. `Q4(l) < 212 366 032 807 211`. -/
def example44_check : Prop := ∀ l : ℕ, 1 ≤ l → l < 102225496 → Q4 l < 212366032807211

/-- The reduction: the finite check and Theorem 4 give the example. -/
def example44_reduction : Prop := example44_check → example44

end LaboHH
