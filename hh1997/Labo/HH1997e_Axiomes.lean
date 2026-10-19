import Labo.HH1997e_Preuves
import Labo.HH1997d_Fin_Preuves
import Labo.HH1997d_Fort_Preuves

/-!
# LABO-COLLATZ · HH1997e — axiom log of (A′) ⇔ ¬(A), and a final joint check of all batches (a, b, c, d, e)

Output committed in `HH1997e_axioms_v4.34.txt`.
-/

open LaboHH

example : Aprime_equiv := Aprime_equiv_thm
-- one representative per batch, in one environment
example : eq4 := eq4_thm
example : lemma9_15 := lemma9_15_thm
example : thm4 := thm4_thm
example : prop2 := prop2_thm
example : lemma6 := lemma6_thm
example : thm3 := thm3_thm
example : thm1_all_k := thm1_all_k_thm

#print axioms Aprime_equiv_thm
#print axioms cycle_one
#print axioms cycle_two
