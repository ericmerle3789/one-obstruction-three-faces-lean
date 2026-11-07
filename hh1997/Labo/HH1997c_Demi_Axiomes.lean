import Labo.HH1997c_Demi_Preuves

/-!
# LABO-COLLATZ · HH1997c_Demi — axiom log and statement check

The `example` checks that the proof has EXACTLY the type of the frozen statement `remark1_large` of
`Labo/HH1997c_Enonces.lean` (unchanged); each `#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.
-/

open LaboHH

example : remark1_large := remark1_large_thm

#print axioms remark1_large_thm
#print axioms M_closed
#print axioms M_real_form
#print axioms suffix_dom
#print axioms nprime_ge
#print axioms log_bound
#print axioms half_core
