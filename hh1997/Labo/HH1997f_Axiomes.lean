import Labo.HH1997f_Preuves

/-!
# LABO-COLLATZ · HH1997f — axiom log and statement check

Each `example` checks that the proof has EXACTLY the type of the frozen statement (`Labo/HH1997f_Enonces.lean`,
sha256 56a813db…; `example44_check` and `example44` from `Labo/HH1997c_Enonces.lean`, sha256 ea5dfcd3…);
each `#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.
The kernel computations use `decide +kernel` (GMP arithmetic in the kernel), never `native_decide`.
Output committed in `HH1997f_axioms_v4.34.txt`.
-/

open LaboHH

example : stilde_append := stilde_append_thm
example : stilde_wpow := stilde_wpow_thm
example : phi_lt_append := phi_lt_append_thm
example : M_half := M_half_thm
example : example44_step2 := example44_step2_thm
example : example44_step2_star := example44_step2_star_thm
example : example44_step3 := example44_step3_thm
example : example44_A := example44_A_thm
example : example44_check := example44_check_thm
example : example44 := example44_thm
example : example44_Lm := example44_Lm_thm

#print axioms stilde_append_thm
#print axioms stilde_wpow_thm
#print axioms phi_lt_append_thm
#print axioms M_half_thm
#print axioms example44_step2_thm
#print axioms example44_step2_star_thm
#print axioms example44_step3_thm
#print axioms example44_A_thm
#print axioms example44_check_thm
#print axioms example44_thm
#print axioms example44_Lm_thm
