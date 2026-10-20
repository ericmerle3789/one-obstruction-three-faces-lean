import Mathlib
import Lagarias.L1990_Enonces

/-!
# Lagarias 1990 · FROZEN STATEMENTS · addenda after the adversarial review (2026-10-20)

Three points of the review, checked numerically (labtrace id=459) before these statements were written:

| paper | Lean | note |
|---|---|---|
| proof of Thm 4.1 (p. 48): "at most `m` choices of `w`", `F(n,M) ≤ m·2^{n−m}` | `thm4_1_printed_step_m1` | TRUE for `m ≥ 1`: the word of weight 0 has `N = 0` and excludes every other head from its class; the printed justification (one head per weight `0…m`) is loose, and the bound fails only for `m = 0` (`M = 2`, see `thm4_1_printed_step_false`) |
| p. 39: "`T` does not change the denominator" | `den_formal` | true for the FORMAL denominator `q` of `a/q` (`q` odd); false for the reduced one (`den_printed_false`) |
| p. 44: the smallest member of a primitive cycle is always `≡ ±1 (mod 6)` | `min_neg_printed_false` | false for negative cycles if "smallest" means the minimum: the cycle `{−5, −7, −10}` of `T_1` has minimum `−10 ≡ 2 (mod 6)`; `min_pm1` states it for positive cycles |
-/

namespace Lagarias

open LaboBP LaboHH

/-- Proof of Theorem 4.1, the printed count, for `m ≥ 1`. -/
def thm4_1_printed_step_m1 : Prop :=
  ∀ n M m : ℕ, 0 < M → Nat.Coprime M 3 → 1 ≤ m → m ≤ n → 3 ^ m ≤ M → ∀ r, cntRes n M r ≤ m * 2 ^ (n - m)

/-- p. 39, read with the formal denominator. -/
def den_formal : Prop :=
  ∀ a q : ℤ, Odd q → ∃ a' : ℤ, collatzQ ((a : ℚ) / q) = (a' : ℚ) / q

/-- p. 44, for negative cycles. -/
def min_neg_printed_false : Prop :=
  ∃ n : ℤ, n < 0 ∧ InPrimCycle 1 n ∧ (∀ j, n ≤ (Tk 1)^[j] n) ∧ n % 6 = 2

end Lagarias
