import Sdw2005.Sdw_Enonces
import Sdw2005.Chaine
import Sdw2005.Bornes
import Sdw2005.Cycles
import Sdw2005.Sdw91_Enonces
import Sdw2005.Borne91

/-!
# Sdw2005 · statement check and axiom report

Each `example` checks that a proof has exactly the type of its frozen statement (`Sdw2005/Sdw_Enonces.lean`,
`Sdw2005/Sdw91_Enonces.lean`); `#print axioms` follows. `check.sh` fails if one of the 9 theorems below depends on an
axiom other than `propext`, `Classical.choice`, `Quot.sound` (this also rules out `sorryAx`, and the auxiliary axiom
that `native_decide` adds on Lean 4.34).
-/

namespace Sdw2005

example : lemma4 := lemma4_thm
example : lemma6 := lemma6_thm
example : lemma7_min := lemma7_min_thm
example : lemma7 := lemma7_thm
example : chain_K_lt := chain_K_lt_thm
example : cycle_chain := cycle_chain_thm
example : cycle_K_lt := cycle_K_lt_thm
example : chain_K_lt_91 := chain_K_lt_91_thm
example : cycle_K_lt_91 := cycle_K_lt_91_thm

#print axioms lemma4_thm
#print axioms lemma6_thm
#print axioms lemma7_min_thm
#print axioms lemma7_thm
#print axioms chain_K_lt_thm
#print axioms cycle_chain_thm
#print axioms cycle_K_lt_thm
#print axioms chain_K_lt_91_thm
#print axioms cycle_K_lt_91_thm

end Sdw2005
