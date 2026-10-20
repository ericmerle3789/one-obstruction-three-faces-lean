import Mathlib
import Lagarias.Addenda3_Enonces

/-!
# Lagarias 1990 · addendum 3 · proof of `eq4_4_attained`

`N(1^{n+1}) = 3ⁿ + 2·N(1ⁿ)` (definition of `LaboBP.C`), and `3ⁿ + 2(3ⁿ − 2ⁿ) = 3^{n+1} − 2^{n+1}`.
Statement: `Lagarias/Addenda3_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP

theorem eq4_4_attained_thm : eq4_4_attained := by
  intro n
  induction n with
  | zero => simp [C]
  | succ n ih =>
    simp only [List.replicate_succ, C, ↓reduceIte, List.count_replicate_self]
    push_cast
    rw [ih]
    ring

end Lagarias
