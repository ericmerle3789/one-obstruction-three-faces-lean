import Brox2000.Brox_Enonces
import Brox2000.Combinatoire
import Brox2000.Analyse
import Brox2000.Brox

/-!
# Brox2000 · statement check and axiom report

Each `example` checks that a proof has exactly the type of its frozen statement (`Brox2000/Brox_Enonces.lean`);
`#print axioms` follows. `check.sh` fails if one of the 5 theorems below depends on an axiom other than `propext`,
`Classical.choice`, `Quot.sound` (this also rules out `sorryAx`, and the auxiliary axiom that `native_decide` adds on
Lean 4.34).
-/

namespace Brox2000

example : lemma22_pos := lemma22_pos_thm
example : lemma22_finite_pos := lemma22_finite_pos_thm
example : thm11_pos_explicit := thm11_pos_explicit_thm
example : thm11_pos := thm11_pos_thm
example : cor12_pos := cor12_pos_thm

#print axioms lemma22_pos_thm
#print axioms lemma22_finite_pos_thm
#print axioms thm11_pos_explicit_thm
#print axioms thm11_pos_thm
#print axioms cor12_pos_thm

end Brox2000
