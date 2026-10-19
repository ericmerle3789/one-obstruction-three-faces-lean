import Labo.HH1997d_Fin_Preuves
import Labo.HH1997d_Fort_Preuves

/-!
# LABO-COLLATZ · HH1997d — axiom log: Theorem 3 unconditional, and the §4 results in ONE environment

Imports batches a, b, c, d together (no name clash), checks the exact frozen types and prints the axioms of the
main results of §4: Lemma 8, Theorems 1–3, the counterexample to "optimal".  Output: `HH1997d_Fin_axioms_v4.34.txt`.
-/

open LaboHH

example : thm3 := thm3_thm
example : lemma8 := lemma8_thm
example : thm1 := thm1_thm
example : thm1_all_k := thm1_all_k_thm
example : thm2 := thm2_thm
example : thm2_gen := thm2_gen_thm
example : opt_counterexample := opt_counterexample_thm
example : prop2 := prop2_thm
example : lemma6 := lemma6_thm

#print axioms thm3_thm
#print axioms lemma8_thm
#print axioms thm1_thm
#print axioms thm1_all_k_thm
#print axioms thm2_thm
#print axioms thm2_gen_thm
#print axioms opt_counterexample_thm
