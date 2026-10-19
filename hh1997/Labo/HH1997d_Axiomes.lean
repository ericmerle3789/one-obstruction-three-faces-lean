import Labo.HH1997d_Preuves

/-!
# LABO-COLLATZ · HH1997d — axiom log and statement check (fourth batch: §4.1–4.3)

Each `example` checks that the proof has EXACTLY the type of the frozen statement of `Labo/HH1997d_Enonces.lean`
(sha256 d2237ce0…); each `#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.
`thm1_cond` and `thm3_cond` are implications: their hypotheses (`cf_gap`, `18 ≤ q₄ + q₅`, `thm3_line`) are named
`Prop`s, never axioms.  Output committed in `HH1997d_axioms_v4.34.txt`.
-/

open LaboHH

example : prod_formula := prod_formula_thm
example : prod_ineq := prod_ineq_thm
example : lemma8 := lemma8_thm
example : lemma8_gen := lemma8_gen_thm
example : cf_size := cf_size_thm
example : thm1_cond := thm1_cond_thm
example : thm2 := thm2_thm
example : thm2_gen := thm2_gen_thm
example : thm3_last := thm3_last_thm
example : thm3_cond := thm3_cond_thm
example : opt_counterexample := opt_counterexample_thm

#print axioms prod_formula_thm
#print axioms prod_ineq_thm
#print axioms lemma8_thm
#print axioms lemma8_gen_thm
#print axioms cf_size_thm
#print axioms thm1_cond_thm
#print axioms thm2_thm
#print axioms thm2_gen_thm
#print axioms thm3_last_thm
#print axioms thm3_cond_thm
#print axioms opt_counterexample_thm
