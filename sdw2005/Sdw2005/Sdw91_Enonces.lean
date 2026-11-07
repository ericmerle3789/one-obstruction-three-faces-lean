import Mathlib
import Sdw2005.Sdw_Enonces

/-!
# Sdw2005 · FROZEN STATEMENTS, step 2: `m ≤ 91`

Written before the proofs (committed alone), after the statements of `Sdw2005/Sdw_Enonces.lean` and their proofs.
The same bound as `Sdw2005.chain_K_lt` and `Sdw2005.cycle_K_lt` for `m ≤ 91` instead of `m ≤ 82`, with `2·10^21`
instead of `4·10^18`, without any hypothesis.
-/

namespace Sdw2005

/-- For every solution of the chain equation with `m ≤ 91`: `K < 2·10^21`. -/
def chain_K_lt_91 : Prop :=
  ∀ (m : ℕ) (k l a : ℕ → ℕ), ChainSol m k l a → m ≤ 91 → Ksum m k < 2 * 10 ^ 21

/-- A cycle of `C` on the positive integers with at most `91` local minima in `N` terms has fewer than `2·10^21` odd
terms among them. -/
def cycle_K_lt_91 : Prop :=
  ∀ n N : ℕ, 0 < n → 0 < N → C^[N] n = n → minCount n N ≤ 91 → oddCount n N < 2 * 10 ^ 21

end Sdw2005
