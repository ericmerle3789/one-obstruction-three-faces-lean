import Mathlib
import Labo.HH1997c_Enonces
import Labo.HH1997d_Enonces

/-!
# LABO-COLLATZ · HH1997d · formaliste (2026-10-19) — FROZEN STATEMENTS, bridges (fourth batch, part 2)

Frozen BEFORE the proofs (`Labo/HH1997d_Pont_Preuves.lean`).  Builds on the frozen files `HH1997c_Enonces`
(batch c, sha256 ea5dfcd3…, by the sibling session: `prop2`, `lemma6`) and `HH1997d_Enonces` (d2237ce0…), not modified.

| target | Lean | note |
|---|---|---|
| Th. 1 from the continued-fraction gap alone (no size hypothesis `18 ≤ q₄ + q₅`) | `thm1_cond_gap` | route: Eliahou's `2^l ≤ (3 + 1/m)^n` gives `l − nθ ≤ n/(3m log 2)`; with the gap and `n ≤ 2m/S` this forces `log 2 < 2/3` |
| the gap for every `k ≥ 1` (best approximation + `|q_kθ − p_k| > 1/(q_k + q_{k+1})`) | `cf_gap_all` | target; proved or not, the report says which |
| Th. 1, unconditional | `thm1_from_gap_all` | `cf_gap_all → thm1`, i.e. `thm1` as soon as `cf_gap_all` is proved |
| the displayed line of Th. 3 from Prop. 2 and Lemma 6 (batch c) | `thm3_line_of` | `prop2 → lemma6 → thm3_line` |
| Th. 3 from Prop. 2 and Lemma 6 | `thm3_of` | `prop2 → lemma6 → thm3` |
-/

namespace LaboHH

/-- Theorem 1 from the continued-fraction gap alone. -/
def thm1_cond_gap : Prop := (∀ k : ℕ, 4 ≤ k → cf_gap k) → thm1

/-- The continued-fraction gap of `log₂ 3` at every index `k ≥ 1`. -/
def cf_gap_all : Prop := ∀ k : ℕ, 1 ≤ k → cf_gap k

/-- Theorem 1 once the gap is known. -/
def thm1_from_gap_all : Prop := cf_gap_all → thm1

/-- The displayed line of the proof of Theorem 3, from Prop. 2 and Lemma 6. -/
def thm3_line_of : Prop := prop2 → lemma6 → thm3_line

/-- Theorem 3 from Prop. 2 and Lemma 6. -/
def thm3_of : Prop := prop2 → lemma6 → thm3

end LaboHH
