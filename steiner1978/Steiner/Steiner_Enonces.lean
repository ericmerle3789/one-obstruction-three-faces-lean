import Mathlib
import Labo.Blueprint

/-!
# Steiner 1978 · FROZEN STATEMENTS

R. P. Steiner, *A theorem on the Syracuse problem*, Proc. 7th Manitoba Conference on Numerical Mathematics and
Computing (1977), Congressus Numerantium 20 (1978), 553–559.

The original text was not available to us and was not read. The statements below follow published accounts of the
theorem and of its proof:
* [La] J. C. Lagarias, *The 3x+1 problem: an annotated bibliography (1963–1999)*, arXiv math/0309224, entry 158;
* [SdW] J. Simons, B. de Weger, *Theoretical and computational bounds for m-cycles of the 3n+1 problem*,
  Acta Arith. 117 (2005), version 1.44 (2010), §1.4 and Lemma 12;
* [St81] R. Steiner, *On the "Qx + 1 problem," Q odd*, Fibonacci Quart. 19 (1981), 285–288: the same method for
  `q = 5` and `q = 7`, with a reference to the 1978 paper.

Written before the proofs. Each statement is a `def … : Prop`; the proofs are `…_thm` in the proof files, and
`Steiner/Axiomes.lean` checks `example : X := X_thm`.

| account | Lean | deviation |
|---|---|---|
| [La]: a circuit is a sequence of iterates, odd `n₁ … n_j` then even `n_{j+1} … n_p`, with `n_{p+1} = T(n_p)` odd; a cycle if `n_{p+1} = n₁` | `CircuitCycle n k l` (`n = n₁`, `k = j`, `l = p − j`) | `l = 0` is allowed (the bracketed remark of [La] counts `{−1}`); `1 ≤ k` is a hypothesis of each statement |
| [La]: circuit-cycles correspond to solutions of `(2^{k+l} − 3^k)h = 2^l − 1`, `h = (n+1)/2^k` | `circuit_iff` | for every `n ∈ ℤ`, `k ≥ 1`, `l ≥ 0`, `h ∈ ℤ` |
| [SdW] §1.4: `0 < (k+ℓ) log 2 − k log 3 < 1/x_min`; [St81] (4): `< 1/(2^k − 1)` | `ineq4` | both bounds |
| [SdW] §1.4: `(k+ℓ)/k` "must be a convergent of δ for k ≥ 5" | `convergent4` | `k ≥ 4`, from the inequality alone |
| [SdW] §1.4: an upper bound for `k` from Baker's theorem | `rhin_k_le` | Rhin's bound (named hypothesis `H_Rhin`) instead of Baker's; `k ≤ 108`; also `h < 0` |
| [SdW] §1.4: partial quotients of `δ`, then a numerical computation | `steiner_small` | replaced by an exact check of each `k ≤ 20000`; no hypothesis |
| [La]: the only positive solution is `(1, 1, 1)`; the only circuit on the positive integers that is a cycle is `{1, 2}` | `steiner`, `steiner_cycle` | under `H_Rhin` |
| [La], in brackets: on the nonpositive integers, `{−1}` and `{−5, −7, −10}`, solutions `(k, 0, 0)` and `(2, 1, −1)` | `steiner_int`, `steiner_cycle_int` | under `H_Rhin` |
| — | `steiner_cycle_small`, `circuit_large` | no hypothesis |
| `Labo/Blueprint.lean`: the open target T★ | `tstar_circuit` | T★ for the words `1^k 0^l`, under `H_Rhin` |
-/

namespace Steiner

open LaboBP

/-- A circuit that is a cycle: from `n`, `k` odd iterates of `T`, then `l` even iterates, then back to `n`. -/
def CircuitCycle (n : ℤ) (k l : ℕ) : Prop :=
  (∀ i < k, Odd (T^[i] n)) ∧ (∀ i < l, Even (T^[k + i] n)) ∧ T^[k + l] n = n

/-- Davison's equation `(2^(k+l) − 3^k)·h = 2^l − 1`. -/
def DavisonEq (k l : ℕ) (h : ℤ) : Prop :=
  ((2 : ℤ) ^ (k + l) - 3 ^ k) * h = 2 ^ l - 1

/-- The parity word `1^k 0^l` (`true` = odd step). -/
def oneBlock (k l : ℕ) : List Bool := List.replicate k true ++ List.replicate l false

/-- The linear form `Λ = (k + l) log 2 − k log 3` (natural logarithms). -/
noncomputable def Lam (k l : ℕ) : ℝ := ((k + l : ℕ) : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3

/-- **Named hypothesis**, never proved here: G. Rhin, *Approximants de Padé et mesures effectives
d'irrationalité*, Progress in Math. 71 (1987), 155–164, Proposition p. 160, inequality (7), in the case `u₀ = 0`:
for integers `u₁, u₂` with `H = max(|u₁|, |u₂|) ≥ 2`, `|u₁ log 2 + u₂ log 3| ≥ H^(−13.3)`. -/
def H_Rhin : Prop :=
  ∀ u₁ u₂ : ℤ, 2 ≤ max |u₁| |u₂| →
    ((max |u₁| |u₂| : ℤ) : ℝ) ^ (-(133 / 10 : ℝ)) ≤ |(u₁ : ℝ) * Real.log 2 + (u₂ : ℝ) * Real.log 3|

/-- Davison's correspondence: circuit-cycles are the solutions of Davison's equation, with `n + 1 = 2^k h`. -/
def circuit_iff : Prop :=
  ∀ (n : ℤ) (k l : ℕ), 1 ≤ k → (CircuitCycle n k l ↔ ∃ h : ℤ, n + 1 = 2 ^ k * h ∧ DavisonEq k l h)

/-- The inequality: `0 < Λ < 1/(2^k h − 1) ≤ 1/(2^k − 1)`, where `2^k h − 1` is the smallest element `n`. -/
def ineq4 : Prop :=
  ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → 1 ≤ l → 1 ≤ h → DavisonEq k l h →
    0 < Lam k l ∧ Lam k l < 1 / ((2 : ℝ) ^ k * h - 1) ∧ 1 / ((2 : ℝ) ^ k * h - 1) ≤ 1 / ((2 : ℝ) ^ k - 1)

/-- For `k ≥ 4`, the inequality forces `(k + l)/k` to be a convergent of `log₂ 3`. -/
def convergent4 : Prop :=
  ∀ k l : ℕ, 4 ≤ k → 0 < Lam k l → Lam k l < 1 / ((2 : ℝ) ^ k - 1) →
    ∃ m : ℕ, ((k + l : ℕ) : ℚ) / k = (Real.logb 2 3).convergent m

/-- Under Rhin's bound, every solution with `l ≥ 1` and `h ≠ 0` has `k ≤ 108`. -/
def rhin_k_le : Prop :=
  H_Rhin → ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → 1 ≤ l → h ≠ 0 → DavisonEq k l h → k ≤ 108

/-- Without any hypothesis: for `k ≤ 20000`, the only positive solution is `(1, 1, 1)`. -/
def steiner_small : Prop :=
  ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → k ≤ 20000 → 1 ≤ l → 1 ≤ h → DavisonEq k l h → k = 1 ∧ l = 1 ∧ h = 1

/-- **Steiner's theorem** (under `H_Rhin`): the only positive solution of Davison's equation is `(1, 1, 1)`. -/
def steiner : Prop :=
  H_Rhin → ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → 1 ≤ l → 1 ≤ h → DavisonEq k l h → k = 1 ∧ l = 1 ∧ h = 1

/-- All integer solutions with `k ≥ 1` (under `H_Rhin`). -/
def steiner_int : Prop :=
  H_Rhin → ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → DavisonEq k l h →
    (l = 0 ∧ h = 0) ∨ (k = 1 ∧ l = 1 ∧ h = 1) ∨ (k = 2 ∧ l = 1 ∧ h = -1)

/-- **Steiner's theorem, dynamical form** (under `H_Rhin`): the only circuit on the positive integers that is a
cycle is `{1, 2}`. -/
def steiner_cycle : Prop :=
  H_Rhin → ∀ (n : ℤ) (k l : ℕ), 0 < n → 1 ≤ k → CircuitCycle n k l → n = 1 ∧ k = 1 ∧ l = 1

/-- Without any hypothesis, for `k ≤ 20000`. -/
def steiner_cycle_small : Prop :=
  ∀ (n : ℤ) (k l : ℕ), 0 < n → 1 ≤ k → k ≤ 20000 → CircuitCycle n k l → n = 1 ∧ k = 1 ∧ l = 1

/-- All circuit-cycles on `ℤ` (under `H_Rhin`): `{−1}`, `{1, 2}`, `{−5, −7, −10}`. -/
def steiner_cycle_int : Prop :=
  H_Rhin → ∀ (n : ℤ) (k l : ℕ), 1 ≤ k → CircuitCycle n k l →
    (n = -1 ∧ l = 0) ∨ (n = 1 ∧ k = 1 ∧ l = 1) ∨ (n = -5 ∧ k = 2 ∧ l = 1)

/-- Without any hypothesis: a circuit-cycle on the positive integers other than `{1, 2}` starts at
`n ≥ 2^20001 − 1`. -/
def circuit_large : Prop :=
  ∀ (n : ℤ) (k l : ℕ), 0 < n → 1 ≤ k → CircuitCycle n k l → n ≠ 1 → 2 ^ 20001 - 1 ≤ n

/-- T★ (`LaboBP.Tstar`) for the words `1^k 0^l` (under `H_Rhin`). -/
def tstar_circuit : Prop :=
  H_Rhin → ∀ k l : ℕ, 0 < d (oneBlock k l) → true ∈ oneBlock k l →
    d (oneBlock k l) ∣ (C (oneBlock k l) : ℤ) → TrivialWord (oneBlock k l)

end Steiner
