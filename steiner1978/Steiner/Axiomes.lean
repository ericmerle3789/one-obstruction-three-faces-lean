import Steiner.Dynamique
import Steiner.Fini
import Steiner.Analyse
import Steiner.Principal

/-!
# Steiner 1978 · statement check and axiom report

Each `example` checks that a proof has exactly the type of its frozen statement; `#print axioms` follows.
`check.sh` fails if any theorem depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`
(this also rules out `sorryAx`, and the auxiliary axiom `<name>._native.native_decide.ax_…` that `native_decide`
adds on Lean 4.34).
The named hypothesis `H_Rhin` is not an axiom: it appears as the premise `H_Rhin → …` of the statements that
use it.
-/

namespace Steiner

example : circuit_iff := circuit_iff_thm
example : ineq4 := ineq4_thm
example : convergent4 := convergent4_thm
example : rhin_k_le := rhin_k_le_thm
example : steiner_small := steiner_small_thm
example : steiner := steiner_thm
example : steiner_int := steiner_int_thm
example : steiner_cycle := steiner_cycle_thm
example : steiner_cycle_small := steiner_cycle_small_thm
example : steiner_cycle_int := steiner_cycle_int_thm
example : circuit_large := circuit_large_thm
example : tstar_circuit := tstar_circuit_thm

#print axioms circuit_iff_thm
#print axioms ineq4_thm
#print axioms convergent4_thm
#print axioms rhin_k_le_thm
#print axioms steiner_small_thm
#print axioms steiner_thm
#print axioms steiner_int_thm
#print axioms steiner_cycle_thm
#print axioms steiner_cycle_small_thm
#print axioms steiner_cycle_int_thm
#print axioms circuit_large_thm
#print axioms tstar_circuit_thm

end Steiner
