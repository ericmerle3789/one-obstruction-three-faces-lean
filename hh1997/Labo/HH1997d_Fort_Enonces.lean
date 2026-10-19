import Mathlib
import Labo.HH1997d_Enonces

/-!
# LABO-COLLATZ · HH1997d · formaliste (2026-10-19) — FROZEN STATEMENT: Theorem 1 for every `k`

Frozen BEFORE the proof (`Labo/HH1997d_Fort_Preuves.lean`).  Builds on `HH1997d_Enonces` (d2237ce0…), not modified.

| paper | Lean | deviation |
|---|---|---|
| Th. 1 (Crandall), "for `k > 4`" | `thm1_all_k` | every `k ≥ 0` (stronger than printed: the condition `k > 4` is not needed; for `k = 0`, `q₀ = 1 < 2 ≤ n`) |
-/

namespace LaboHH

open LaboBP

/-- Theorem 1 for every index `k` (Mathlib's indexing, `q₀ = 1`). -/
def thm1_all_k : Prop :=
  ∀ k : ℕ, ∀ (l n : ℕ) (s : List Bool), s ∈ Sln l n → n ≤ nOf l →
    ∀ m : ℚ, 1 < m → IsLeast (cycle ((phi s : ℚ) / (d s : ℚ))) m →
      min (qCF k) (2 * (m : ℝ) / (qCF k + qCF (k + 1))) < n

end LaboHH
