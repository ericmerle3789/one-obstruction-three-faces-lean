import Mathlib
import Steiner.Steiner_Enonces

/-!
# Logs23 · FROZEN STATEMENTS of step 2b (a lower bound for linear forms in `log 2` and `log 3`)

Written before the proofs (committed alone), after the statements of step 2a (`Logs23/Logs23_Enonces.lean`).

`two_log_lower` is an explicit lower bound of polylogarithmic type for `|b₁ log 2 − b₂ log 3|`, for `b₂ ≥ 2^334`.
Much stronger explicit bounds are known (M. Laurent, Acta Arith. 66 (1994); M. Laurent, M. Mignotte,
Y. Nesterenko, J. Number Theory 55 (1995); N. Gouillon, J. Théor. Nombres Bordeaux 18 (2006)); the constant
`10^12` and the exponent `5` are chosen so that the proof can be crude. The planned proof (an interpolation
determinant whose zero lemma is replaced by total positivity) is described in the lab's register, not here.

`lam_lower_large` is the case `k ≥ 2^334` of `Logs23.lam_lower`; together with `Logs23.lam_lower_bridge`
(`20000 < k < qBr'`, and `2^334 < qBr'`) it gives `Logs23.lam_lower`, hence, by `Logs23.reduction`, Steiner's
theorem without hypothesis.

| Lean | content |
|---|---|
| `two_log_lower` | `b₂ ≥ 2^334` ⇒ `exp(−10^12 ν^5) ≤ \|b₁ log 2 − b₂ log 3\|`, `ν = ⌊log₂ b₂⌋ + 1` (`Nat.log 2 b₂ + 1`), every `b₁ ≥ 0` |
| `lam_lower_large` | `k ≥ 2^334` ⇒ `1/(2^k − 1) ≤ \|Λ\|`, `Λ = (k + l) log 2 − k log 3`, every `l ≥ 0` |
-/

namespace Logs23

open Steiner

/-- An explicit lower bound for `|b₁ log 2 − b₂ log 3|` when `b₂ ≥ 2^334`, with `ν = Nat.log 2 b₂ + 1`. -/
def two_log_lower : Prop :=
  ∀ b₁ b₂ : ℕ, 2 ^ 334 ≤ b₂ →
    Real.exp (-(10 ^ 12 * ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5)) ≤
      |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3|

/-- The lower bound for `Λ` needed by Steiner's theorem, for `k ≥ 2^334`. -/
def lam_lower_large : Prop :=
  ∀ k l : ℕ, 2 ^ 334 ≤ k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|

end Logs23
