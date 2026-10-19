import Mathlib
import Labo.HH1997c_Preuves
import Labo.HH1997d_Pont_Preuves

/-!
# LABO-COLLATZ · HH1997d · formaliste (2026-10-19) — Theorem 3, unconditional

`thm3` is frozen in `Labo/HH1997d_Enonces.lean` (sha256 d2237ce0…).  Its proof: the bridge `thm3_of_thm`
(`prop2 → lemma6 → thm3`, `Labo/HH1997d_Pont_Preuves.lean`) applied to `prop2_thm` and `lemma6_thm`, proved by the
sibling session in `Labo/HH1997c_Preuves.lean` (statements `Labo/HH1997c_Enonces.lean`, sha256 ea5dfcd3…).
-/

namespace LaboHH

/-- Theorem 3 (Eliahou improved): for every positive cycle `C` in `ℚ_(2)` with `|C| > 160`, `|C| ≥ k(min C / 0.9)`. -/
theorem thm3_thm : thm3 := thm3_of_thm prop2_thm lemma6_thm

end LaboHH
