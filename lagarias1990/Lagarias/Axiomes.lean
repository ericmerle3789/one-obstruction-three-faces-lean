import Lagarias.Tables
import Lagarias.L4_Preuves
import Lagarias.L3b_Preuves
import Lagarias.L4b_Preuves
import Lagarias.Addenda
import Lagarias.L2b_Preuves
import Lagarias.L4c_Preuves

/-!
# Lagarias 1990 · statement check and axiom report (phases 2a, 2b, 2c)

Each `example` checks that a proof has exactly the type of its frozen statement; `#print axioms` follows.
`check.sh` fails if any theorem depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`
(this also rules out `sorryAx` and `Lean.ofReduceBool`, the axiom behind `native_decide`).
-/

namespace Lagarias

example : thm2_1 := thm2_1_thm
example : eq2_1 := eq2_1_thm
example : eq1_3 := eq1_3_thm
example : cor2_1a_words := cor2_1a_words_thm
example : cor2_1a := cor2_1a_coppersmith
example : cor2_1a := cor2_1a_lagarias
example : ex_p37 := ex_p37_thm
example : den_step := den_step_thm
example : den_printed_false := den_printed_false_thm
example : den_cycle := den_cycle_thm
example : delta_eq := delta_eq_thm
example : dichotomy := dichotomy_thm
example : bseq_inj := bseq_inj_thm
example : cor2_1b := cor2_1b_thm
example : clear_den := clear_den_thm
example : D6_printed_false := D6_printed_false_thm
example : D6 := D6_thm
example : tk_sign_printed_false := tk_sign_printed_false_thm
example : tk_sign := tk_sign_thm
example : tk_Z_printed_false := tk_Z_printed_false_thm
example : tk_Z := tk_Z_thm
example : tk_scale := tk_scale_thm
example : bij3 := bij3_thm
example : no3 := no3_thm
example : min_pm1 := min_pm1_thm
example : eq3_8 := eq3_8_thm
example : thm3_5 := thm3_5_thm
example : ex_10m := ex_10m_thm
example : ex_5 := ex_5_thm
example : thm3_4 := thm3_4_thm
example : eq4_4_printed_false := eq4_4_printed_false_thm
example : eq4_4 := eq4_4_thm
example : eq4_5 := eq4_5_thm
example : eq4_8 := eq4_8_thm
example : thm4_1_core := thm4_1_core_thm
example : thm4_1_printed_step_false := thm4_1_printed_step_false_thm
example : thm4_1 := thm4_1_thm
example : table2_2_values := table2_2_values_thm
example : table2_2_complete := table2_2_complete_thm
example : table2_2_gcd := table2_2_gcd_thm
example : table3_1_rows := table3_1_rows_thm
example : table3_1_row35 := table3_1_row35_thm
example : table3_1_row73 := table3_1_row73_thm
example : p41 := p41_thm
example : thm3_3_count_printed_false := thm3_3_count_printed_false_thm
example : k_dvd_D := k_dvd_D_thm
example : S31_bound := S31_bound_thm
example : thm3_1 := thm3_1_thm
example : thm3_1_65 := thm3_1_65_thm
example : thm3_2 := thm3_2_thm
example : ash_tail := ash_tail_thm
example : thm4_2 := thm4_2_thm
example : thm4_1_printed_step_m1 := thm4_1_printed_step_m1_thm
example : den_formal := den_formal_thm
example : min_neg_printed_false := min_neg_printed_false_thm
example : eq2_4 := eq2_4_thm
example : eq2_5 := eq2_5_thm
example : table2_1 := table2_1_thm
example : thm4_2_printed := thm4_2_printed_thm

end Lagarias

#print axioms Lagarias.thm2_1_thm
#print axioms Lagarias.eq2_1_thm
#print axioms Lagarias.eq1_3_thm
#print axioms Lagarias.cor2_1a_words_thm
#print axioms Lagarias.cor2_1a_coppersmith
#print axioms Lagarias.cor2_1a_lagarias
#print axioms Lagarias.ex_p37_thm
#print axioms Lagarias.den_step_thm
#print axioms Lagarias.den_printed_false_thm
#print axioms Lagarias.den_cycle_thm
#print axioms Lagarias.delta_eq_thm
#print axioms Lagarias.dichotomy_thm
#print axioms Lagarias.bseq_inj_thm
#print axioms Lagarias.cor2_1b_thm
#print axioms Lagarias.clear_den_thm
#print axioms Lagarias.D6_printed_false_thm
#print axioms Lagarias.D6_thm
#print axioms Lagarias.tk_sign_printed_false_thm
#print axioms Lagarias.tk_sign_thm
#print axioms Lagarias.tk_Z_printed_false_thm
#print axioms Lagarias.tk_Z_thm
#print axioms Lagarias.tk_scale_thm
#print axioms Lagarias.bij3_thm
#print axioms Lagarias.no3_thm
#print axioms Lagarias.min_pm1_thm
#print axioms Lagarias.eq3_8_thm
#print axioms Lagarias.thm3_5_thm
#print axioms Lagarias.ex_10m_thm
#print axioms Lagarias.ex_5_thm
#print axioms Lagarias.thm3_4_thm
#print axioms Lagarias.eq4_4_printed_false_thm
#print axioms Lagarias.eq4_4_thm
#print axioms Lagarias.eq4_5_thm
#print axioms Lagarias.eq4_8_thm
#print axioms Lagarias.thm4_1_core_thm
#print axioms Lagarias.thm4_1_printed_step_false_thm
#print axioms Lagarias.thm4_1_thm
#print axioms Lagarias.table2_2_values_thm
#print axioms Lagarias.table2_2_complete_thm
#print axioms Lagarias.table2_2_gcd_thm
#print axioms Lagarias.table3_1_rows_thm
#print axioms Lagarias.table3_1_row35_thm
#print axioms Lagarias.table3_1_row73_thm
#print axioms Lagarias.p41_thm
#print axioms Lagarias.thm3_3_count_printed_false_thm
#print axioms Lagarias.k_dvd_D_thm
#print axioms Lagarias.S31_bound_thm
#print axioms Lagarias.thm3_1_thm
#print axioms Lagarias.thm3_1_65_thm
#print axioms Lagarias.thm3_2_thm
#print axioms Lagarias.ash_tail_thm
#print axioms Lagarias.thm4_2_thm
#print axioms Lagarias.thm4_1_printed_step_m1_thm
#print axioms Lagarias.den_formal_thm
#print axioms Lagarias.min_neg_printed_false_thm
#print axioms Lagarias.eq2_4_thm
#print axioms Lagarias.eq2_5_thm
#print axioms Lagarias.table2_1_thm
#print axioms Lagarias.thm4_2_printed_thm
