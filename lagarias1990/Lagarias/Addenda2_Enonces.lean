import Mathlib
import Lagarias.L1990b_Enonces

/-!
# Lagarias 1990 · FROZEN STATEMENT (addendum 2)

The second adversarial review noted that (2.6) was neither proved nor listed as out of scope.
Written before its proof. Proof: `Lagarias/Addenda2.lean`.

| paper | Lean | deviation |
|---|---|---|
| (2.6) (p. 38): `I(n) = 2ⁿ/n + O(2^{n/2})` | `eq2_6` | the `O` is made explicit: `∃ c, ∀ n ≥ 1, |I(n) − 2ⁿ/n| ≤ c·2^{n/2}` |
-/

namespace Lagarias

/-- (2.6). -/
def eq2_6 : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, 0 < n → |(Iirr n : ℝ) - 2 ^ n / n| ≤ c * 2 ^ ((n : ℝ) / 2)

end Lagarias
