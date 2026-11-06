import Seifert1988.Seifert_Enonces
import Seifert1988.Algebre
import Seifert1988.Dynamique
import Seifert1988.Corollaires
import Seifert1988.Voisins

/-!
# Seifert 1988 · statement check and axiom report

Each `example` checks that a proof has exactly the type of its frozen statement; `#print axioms` follows.
`check.sh` fails if one of the 33 theorems below (the statements of `Seifert1988/Seifert_Enonces.lean`) depends on an
axiom other than `propext`, `Classical.choice`, `Quot.sound` (this also rules out `sorryAx`, and the auxiliary axiom
that `native_decide` adds on Lean 4.34).
-/

namespace Seifert

example : f_maps := f_maps_thm
example : d_neg := d_neg_thm
example : d_perm := d_perm_thm
example : formula_1_2 := formula_1_2_thm
example : formula_1_2' := formula_1_2'_thm
example : lengthVector_pos := lengthVector_pos_thm
example : thm1a_unique := thm1a_unique_thm
example : thm1a_rotate := thm1a_rotate_thm
example : thm1b := thm1b_thm
example : thm1b_single := thm1b_single_thm
example : free_essential := free_essential_thm
example : examples := examples_thm
example : remark_constant := remark_constant_thm
example : printed_e_reverse := printed_e_reverse_thm
example : printed_e_examples := printed_e_examples_thm
example : thm1b_printed_false := thm1b_printed_false_thm
example : thm1b_reversed := thm1b_reversed_thm
example : cor1_difference_printed := cor1_difference_printed_thm
example : cor1_difference := cor1_difference_thm
example : cor1_printed_false := cor1_printed_false_thm
example : cor1_divides := cor1_divides_thm
example : near_miss := near_miss_thm
example : cor1_exact := cor1_exact_thm
example : cor1_exact_anywhere := cor1_exact_anywhere_thm
example : solution_gives_cycle := solution_gives_cycle_thm
example : cor2_plus := cor2_plus_thm
example : cor2_minus := cor2_minus_thm
example : gersonides_plus := gersonides_plus_thm
example : gersonides_minus := gersonides_minus_thm
example : thm2 := thm2_thm
example : thm2_plus := thm2_plus_thm
example : thm2_printed_false := thm2_printed_false_thm
example : thm2_reversed := thm2_reversed_thm

#print axioms f_maps_thm
#print axioms d_neg_thm
#print axioms d_perm_thm
#print axioms formula_1_2_thm
#print axioms formula_1_2'_thm
#print axioms lengthVector_pos_thm
#print axioms thm1a_unique_thm
#print axioms thm1a_rotate_thm
#print axioms thm1b_thm
#print axioms thm1b_single_thm
#print axioms free_essential_thm
#print axioms examples_thm
#print axioms remark_constant_thm
#print axioms printed_e_reverse_thm
#print axioms printed_e_examples_thm
#print axioms thm1b_printed_false_thm
#print axioms thm1b_reversed_thm
#print axioms cor1_difference_printed_thm
#print axioms cor1_difference_thm
#print axioms cor1_printed_false_thm
#print axioms cor1_divides_thm
#print axioms near_miss_thm
#print axioms cor1_exact_thm
#print axioms cor1_exact_anywhere_thm
#print axioms solution_gives_cycle_thm
#print axioms cor2_plus_thm
#print axioms cor2_minus_thm
#print axioms gersonides_plus_thm
#print axioms gersonides_minus_thm
#print axioms thm2_thm
#print axioms thm2_plus_thm
#print axioms thm2_printed_false_thm
#print axioms thm2_reversed_thm

end Seifert
