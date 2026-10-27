import Mathlib
import Steiner.Steiner_Enonces

/-!
# Logs23 · FROZEN STATEMENTS

Goal: remove the named hypothesis `Steiner.H_Rhin` from the Steiner 1978 formalisation (`../steiner1978/`).
That formalisation proves Steiner's theorem under `H_Rhin` (G. Rhin 1987, inequality (7), case `u₀ = 0`), and
without hypothesis only for `k ≤ 20000`. It uses `H_Rhin` only through `rhin_k_le` ("`k ≤ 108`").

What is needed is much weaker than `H_Rhin`: `lam_lower` below, a lower bound `1/(2^k − 1) ≤ |Λ|` for the linear
form `Λ = (k + l) log 2 − k log 3` when `k > 20000`. We do **not** formalise Rhin's paper.

Plan (see `README.md`):
* **step 2a, the bridge** (no hypothesis): two consecutive convergents `pBr/qBr`, `pBr'/qBr'` of `log₂ 3`
  (`qBr` has 100 digits, `qBr'` has 101) give `|L log 2 − k log 3| ≥ |pBr log 2 − qBr log 3| ≥ 10^(−101)` for
  every `0 < k < qBr'` (`bridge_gap`, `bridge_value`), hence `lam_lower` for `20000 < k < qBr'`, and Steiner's
  theorem for `k < qBr'`;
* **step 2b**: an effective lower bound for `|b₁ log 2 − b₂ log 3|` for large `b₂` (`Logs23/TwoLog_Enonces.lean`,
  proved in `Logs23/TwoLog.lean`), giving `lam_lower` for `k ≥ 2^334`, hence for every `k > 20000` with the bridge;
  with `reduction`, Steiner's theorem without any hypothesis.

Written before the proofs. Each statement is a `def … : Prop`; the proofs are `…_thm` in the proof files, and
`Logs23/Axiomes.lean` checks `example : X := X_thm` for the statements proved so far.

| Lean | content | step |
|---|---|---|
| `pBr`, `qBr`, `pBr'`, `qBr'` | the two convergents (definitions; `pBr' * qBr − pBr * qBr' = 1` is part of `bridge_gap`'s proof) | 2a |
| `bridge_gap` | `0 < k < qBr'` ⇒ `\|pBr log 2 − qBr log 3\| ≤ \|L log 2 − k log 3\|` | 2a |
| `bridge_value` | `10^(−101) ≤ \|pBr log 2 − qBr log 3\|` | 2a |
| `lam_lower_bridge` | `20000 < k < qBr'` ⇒ `1/(2^k − 1) ≤ \|Λ\|` | 2a |
| `steiner_bridge`, `steiner_cycle_bridge` | Steiner's theorem for `k < qBr'`, no hypothesis | 2a |
| `reduction` | `lam_lower` ⇒ the five statements `…_nh` | 2a |
| `lam_lower` | `20000 < k` ⇒ `1/(2^k − 1) ≤ \|Λ\|` (**final target**) | 2b |
| `steiner_nh`, `steiner_int_nh`, `steiner_cycle_nh`, `steiner_cycle_int_nh`, `tstar_circuit_nh` | `steiner`, `steiner_int`, `steiner_cycle`, `steiner_cycle_int`, `tstar_circuit` of `../steiner1978/` without the premise `H_Rhin` | 2b |
-/

namespace Logs23

open Steiner LaboBP

/-! ## The bridge -/

/-- Numerator of the convergent of `log₂ 3` with 100-digit denominator `qBr`. -/
def pBr : ℕ :=
  7075648572877059919177282639679936234273371429152254350020918875159741651922223841987201299719166766

/-- The first denominator of a convergent of `log₂ 3` with 100 digits. -/
def qBr : ℕ :=
  4464237210443557913445974161134855053365712428483203741240064204646931348649280801574011068200682601

/-- Numerator of the next convergent. -/
def pBr' : ℕ :=
  100503145492375000798721301105204469272055612770110310199489733016535938908007507750788779148681720787

/-- Denominator of the next convergent (101 digits). -/
def qBr' : ℕ :=
  63410424818660492580825542274682247263205981867410584037516082787822549765875074521441459392200135171

/-- No `L log 2 − k log 3` with `0 < k < qBr'` is closer to `0` than `pBr log 2 − qBr log 3`. -/
def bridge_gap : Prop :=
  ∀ (k : ℕ) (L : ℤ), 0 < k → k < qBr' →
    |(pBr : ℝ) * Real.log 2 - (qBr : ℝ) * Real.log 3| ≤ |(L : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3|

/-- The size of the gap. -/
def bridge_value : Prop :=
  (1 : ℝ) / 10 ^ 101 ≤ |(pBr : ℝ) * Real.log 2 - (qBr : ℝ) * Real.log 3|

/-- The lower bound for `Λ`, for `20000 < k < qBr'`. -/
def lam_lower_bridge : Prop :=
  ∀ k l : ℕ, 20000 < k → k < qBr' → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|

/-- Without any hypothesis, for `k < qBr'`: the only positive solution of Davison's equation is `(1, 1, 1)`. -/
def steiner_bridge : Prop :=
  ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → k < qBr' → 1 ≤ l → 1 ≤ h → DavisonEq k l h → k = 1 ∧ l = 1 ∧ h = 1

/-- Without any hypothesis, for `k < qBr'`: the only circuit on the positive integers that is a cycle is
`{1, 2}`. -/
def steiner_cycle_bridge : Prop :=
  ∀ (n : ℤ) (k l : ℕ), 0 < n → 1 ≤ k → k < qBr' → CircuitCycle n k l → n = 1 ∧ k = 1 ∧ l = 1

/-! ## The final target -/

/-- **Final target**: the lower bound for `Λ`, for every `k > 20000`. -/
def lam_lower : Prop :=
  ∀ k l : ℕ, 20000 < k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|

/-- Steiner's theorem without hypothesis (`Steiner.steiner` without `H_Rhin`). -/
def steiner_nh : Prop :=
  ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → 1 ≤ l → 1 ≤ h → DavisonEq k l h → k = 1 ∧ l = 1 ∧ h = 1

/-- All integer solutions with `k ≥ 1`, without hypothesis (`Steiner.steiner_int` without `H_Rhin`). -/
def steiner_int_nh : Prop :=
  ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → DavisonEq k l h →
    (l = 0 ∧ h = 0) ∨ (k = 1 ∧ l = 1 ∧ h = 1) ∨ (k = 2 ∧ l = 1 ∧ h = -1)

/-- The dynamical form, without hypothesis (`Steiner.steiner_cycle` without `H_Rhin`). -/
def steiner_cycle_nh : Prop :=
  ∀ (n : ℤ) (k l : ℕ), 0 < n → 1 ≤ k → CircuitCycle n k l → n = 1 ∧ k = 1 ∧ l = 1

/-- All circuit-cycles on `ℤ`, without hypothesis (`Steiner.steiner_cycle_int` without `H_Rhin`). -/
def steiner_cycle_int_nh : Prop :=
  ∀ (n : ℤ) (k l : ℕ), 1 ≤ k → CircuitCycle n k l →
    (n = -1 ∧ l = 0) ∨ (n = 1 ∧ k = 1 ∧ l = 1) ∨ (n = -5 ∧ k = 2 ∧ l = 1)

/-- T★ for the words `1^k 0^l`, without hypothesis (`Steiner.tstar_circuit` without `H_Rhin`). -/
def tstar_circuit_nh : Prop :=
  ∀ k l : ℕ, 0 < d (oneBlock k l) → true ∈ oneBlock k l →
    d (oneBlock k l) ∣ (C (oneBlock k l) : ℤ) → TrivialWord (oneBlock k l)

/-- The final target implies the five statements. -/
def reduction : Prop :=
  lam_lower → steiner_nh ∧ steiner_int_nh ∧ steiner_cycle_nh ∧ steiner_cycle_int_nh ∧ tstar_circuit_nh

end Logs23
