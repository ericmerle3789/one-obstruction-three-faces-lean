import Logs23.Logs23_Enonces
import Logs23.Encadrements
import Logs23.Pont
import Logs23.Principal

/-!
# Logs23 · statement check and axiom report

Each `example` checks that a proof has exactly the type of its frozen statement; `#print axioms` follows.
`check.sh` fails if one of the 7 theorems below (the 6 frozen statements proved so far, and `widths`, which backs
the widths of the enclosures quoted in the README) depends on an axiom other than `propext`, `Classical.choice`,
`Quot.sound` (this also rules out `sorryAx`, and the auxiliary axiom that `native_decide` adds on Lean 4.34).

Only the statements proved so far are listed. Not yet proved (step 2b): `lam_lower`, and therefore
`steiner_nh`, `steiner_int_nh`, `steiner_cycle_nh`, `steiner_cycle_int_nh`, `tstar_circuit_nh`
(`reduction` proves them from `lam_lower`).
-/

namespace Logs23

example : bridge_gap := bridge_gap_thm
example : bridge_value := bridge_value_thm
example : lam_lower_bridge := lam_lower_bridge_thm
example : steiner_bridge := steiner_bridge_thm
example : steiner_cycle_bridge := steiner_cycle_bridge_thm
example : reduction := reduction_thm

#print axioms bridge_gap_thm
#print axioms bridge_value_thm
#print axioms lam_lower_bridge_thm
#print axioms steiner_bridge_thm
#print axioms steiner_cycle_bridge_thm
#print axioms reduction_thm
#print axioms widths

end Logs23
