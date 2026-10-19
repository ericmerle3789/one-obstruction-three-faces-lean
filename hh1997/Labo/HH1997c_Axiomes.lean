import Labo.HH1997c_Preuves

/-!
# LABO-COLLATZ · HH1997c — axiom log and statement check

Each `example` checks that the proof has EXACTLY the type of the frozen statement of `Labo/HH1997c_Enonces.lean`;
each `#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.
NOT proved (named, see the report): `remark1_large`, `example44_check` (hence `example44` itself).
Output committed in `HH1997c_axioms_v4.34.txt`.
-/

open LaboHH

example : zero_cycle := zero_cycle_thm
example : lemma1_sign := lemma1_sign_thm
example : prop1 := prop1_thm
example : prop2 := prop2_thm
example : blocks23 := blocks23_thm
example : blocks160 := blocks160_thm
example : lemma6 := lemma6_thm
example : remark1 := remark1_thm
example : remark1_lower6 := remark1_lower6_thm
example : example44_reduction := example44_reduction_thm

#print axioms zero_cycle_thm
#print axioms lemma1_sign_thm
#print axioms prop1_thm
#print axioms prop2_thm
#print axioms blocks23_thm
#print axioms blocks160_thm
#print axioms lemma6_thm
#print axioms remark1_thm
#print axioms remark1_lower6_thm
#print axioms example44_reduction_thm
