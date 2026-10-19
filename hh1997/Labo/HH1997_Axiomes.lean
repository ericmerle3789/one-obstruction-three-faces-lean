import Labo.HH1997_Preuves

/-!
# LABO-COLLATZ · HH1997 — axiom log and statement check

Each `example` checks that the proof has EXACTLY the type of the frozen statement of `Labo/HH1997_Enonces.lean`;
each `#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.
Output committed in `HH1997_axioms_v4.34.txt`.
-/

open LaboHH

example : eq2 := eq2_thm
example : eq3 := eq3_thm
example : eq4 := eq4_thm
example : phi_eq_C := phi_eq_C_thm
example : W0_bridge := W0_bridge_thm
example : eq4_kernel := eq4_kernel_thm
example : lemma2_affine := lemma2_affine_thm
example : lemma2_fixed := lemma2_fixed_thm
example : lemma2_cycle := lemma2_cycle_thm
example : lemma4 := lemma4_thm
example : lemma5 := lemma5_thm
example : cor1 := cor1_thm
example : eq13 := eq13_thm
example : lemma9_14 := lemma9_14_thm
example : lemma9_14_gen := lemma9_14_gen_thm
example : lemma9_15 := lemma9_15_thm
example : lemma9_15_gen := lemma9_15_gen_thm
example : lemma9_core := lemma9_core_thm

#print axioms eq2_thm
#print axioms eq3_thm
#print axioms eq4_thm
#print axioms phi_eq_C_thm
#print axioms W0_bridge_thm
#print axioms eq4_kernel_thm
#print axioms lemma2_affine_thm
#print axioms lemma2_fixed_thm
#print axioms lemma2_cycle_thm
#print axioms lemma4_thm
#print axioms lemma5_thm
#print axioms cor1_thm
#print axioms eq13_thm
#print axioms lemma9_14_thm
#print axioms lemma9_14_gen_thm
#print axioms lemma9_15_thm
#print axioms lemma9_15_gen_thm
#print axioms lemma9_core_thm
