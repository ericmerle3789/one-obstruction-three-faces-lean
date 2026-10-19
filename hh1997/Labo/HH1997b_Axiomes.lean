import Labo.HH1997b_Preuves

/-!
# LABO-COLLATZ · HH1997b — axiom log and statement check (second batch)

Each `example` checks that the proof has EXACTLY the type of the frozen statement of `Labo/HH1997b_Enonces.lean`
(sha256 072bdf35…); each `#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.
Output committed in `HH1997b_axioms_v4.34.txt`.
-/

open LaboHH

example : lemma3 := lemma3_thm
example : lemma3_strong := lemma3_strong_thm
example : lemma7 := lemma7_thm
example : lemma7_dom := lemma7_dom_thm
example : lemma7_step := lemma7_step_thm
example : lemma1 := lemma1_thm
example : nOf_spec := nOf_spec_thm
example : Q4_eq_M := Q4_eq_M_thm
example : eq11 := eq11_thm
example : thm4_core := thm4_core_thm
example : thm4 := thm4_thm

#print axioms lemma3_thm
#print axioms lemma3_strong_thm
#print axioms lemma7_thm
#print axioms lemma7_dom_thm
#print axioms lemma7_step_thm
#print axioms lemma1_thm
#print axioms nOf_spec_thm
#print axioms Q4_eq_M_thm
#print axioms eq11_thm
#print axioms thm4_core_thm
#print axioms thm4_thm
