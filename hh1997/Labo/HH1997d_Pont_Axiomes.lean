import Labo.HH1997d_CF_Preuves

/-!
# LABO-COLLATZ · HH1997d — axiom log and statement check (bridges and continued fractions)

Each `example` checks the exact type of a frozen statement (`Labo/HH1997d_Pont_Enonces.lean`, sha256 fb3c387c…,
and `thm1` of `Labo/HH1997d_Enonces.lean`, sha256 d2237ce0…).  `thm3_line_of`, `thm3_of` are implications whose
hypotheses `prop2`, `lemma6` are frozen statements of batch c (sibling session), never axioms.
Output committed in `HH1997d_Pont_axioms_v4.34.txt`.
-/

open LaboHH

example : thm1_cond_gap := thm1_cond_gap_thm
example : cf_gap_all := cf_gap_all_thm
example : thm1_from_gap_all := thm1_from_gap_all_thm
example : thm1 := thm1_thm
example : thm3_line_of := thm3_line_of_thm
example : thm3_of := thm3_of_thm

#print axioms thm1_cond_gap_thm
#print axioms cf_gap_all_thm
#print axioms thm1_from_gap_all_thm
#print axioms thm1_thm
#print axioms thm3_line_of_thm
#print axioms thm3_of_thm
