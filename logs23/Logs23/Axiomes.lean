import Logs23.Logs23_Enonces
import Logs23.TwoLog_Enonces
import Logs23.Encadrements
import Logs23.Pont
import Logs23.Principal
import Logs23.TwoLog

/-!
# Logs23 · statement check and axiom report

Each `example` checks that a proof has exactly the type of its frozen statement; `#print axioms` follows.
`check.sh` fails if one of the 15 theorems below (the 14 frozen statements of `Logs23/Logs23_Enonces.lean` and
`Logs23/TwoLog_Enonces.lean`, and `widths`, which backs the widths of the enclosures quoted in the README) depends on
an axiom other than `propext`, `Classical.choice`, `Quot.sound` (this also rules out `sorryAx`, and the auxiliary
axiom that `native_decide` adds on Lean 4.34).
-/

namespace Logs23

example : bridge_gap := bridge_gap_thm
example : bridge_value := bridge_value_thm
example : lam_lower_bridge := lam_lower_bridge_thm
example : steiner_bridge := steiner_bridge_thm
example : steiner_cycle_bridge := steiner_cycle_bridge_thm
example : reduction := reduction_thm
example : two_log_lower := two_log_lower_thm
example : lam_lower_large := lam_lower_large_thm
example : lam_lower := lam_lower_thm
example : steiner_nh := steiner_nh_thm
example : steiner_int_nh := steiner_int_nh_thm
example : steiner_cycle_nh := steiner_cycle_nh_thm
example : steiner_cycle_int_nh := steiner_cycle_int_nh_thm
example : tstar_circuit_nh := tstar_circuit_nh_thm

#print axioms bridge_gap_thm
#print axioms bridge_value_thm
#print axioms lam_lower_bridge_thm
#print axioms steiner_bridge_thm
#print axioms steiner_cycle_bridge_thm
#print axioms reduction_thm
#print axioms two_log_lower_thm
#print axioms lam_lower_large_thm
#print axioms lam_lower_thm
#print axioms steiner_nh_thm
#print axioms steiner_int_nh_thm
#print axioms steiner_cycle_nh_thm
#print axioms steiner_cycle_int_nh_thm
#print axioms tstar_circuit_nh_thm
#print axioms widths

end Logs23
