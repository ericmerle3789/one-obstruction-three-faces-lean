import Mathlib
import Lagarias.L1990_Enonces

/-!
# Lagarias 1990 · FROZEN STATEMENT (addendum 3)

The second Red Team pass before release noted that `eq4_4` proves the bound `N(v) ≤ 3ⁿ − 2ⁿ` but not that
`3ⁿ − 2ⁿ` is attained, while its docstring says "the maximum element of `Σ_n`".
Written before its proof. Proof: `Lagarias/Addenda3.lean`.

| paper | Lean | deviation |
|---|---|---|
| p. 47: "The maximum element of `Σ_n` is" (4.4) `= 3ⁿ − 2ⁿ` | `eq4_4_attained` (attained by `v = 1ⁿ`), with the bound `eq4_4` | none |
-/

namespace Lagarias

open LaboBP

/-- (4.4): `N(1ⁿ) = 3ⁿ − 2ⁿ`. -/
def eq4_4_attained : Prop := ∀ n : ℕ, (C (List.replicate n true) : ℤ) = 3 ^ n - 2 ^ n

end Lagarias
