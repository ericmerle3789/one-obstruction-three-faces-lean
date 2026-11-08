import Mathlib
import Sdw2005.Sdw_Enonces

/-!
# Sdw2005 · FROZEN STATEMENTS, step 3: the same bounds counted on distinct values

Written before the proofs (committed alone), after the statements of `Sdw2005/Sdw_Enonces.lean`,
`Sdw2005/Sdw91_Enonces.lean` and their proofs.

`cycle_K_lt` and `cycle_K_lt_91` count odd TERMS and local-minimum TERMS over `N` steps. Some formalisations count
DISTINCT VALUES of the orbit instead (the set `{C^[j] n | j < N}` and its odd elements). These statements give the
same bounds in that form, so that they can be used without re-proving the passage from terms to values:

* `pont_image`, `pont_image_91`: for any `N` with `C^[N] n = n` (no minimality), the number of distinct odd values
  among `C^[j] n`, `j < N`, is below the bound, under the hypothesis on `minCount n N` (local-minimum terms).
* `pont_minimal`, `pont_minimal_91`: over the minimal period `N` of `n` under `C`, the hypothesis is on the number of
  distinct local-minimum values and the conclusion on the number of distinct odd values.

No new mathematics: these are bookkeeping corollaries of `cycle_K_lt` and `cycle_K_lt_91`.
-/

namespace Sdw2005

/-- The distinct values `C^[j] n`, `j < N`. -/
def orbitSet (n N : ℕ) : Finset ℕ := (Finset.range N).image (fun j => C^[j] n)

/-- The distinct odd values among `C^[j] n`, `j < N`. -/
def oddValues (n N : ℕ) : Finset ℕ := (orbitSet n N).filter (fun x => x % 2 = 1)

/-- The distinct local-minimum values among `C^[j] n`, `j < N`: values of the terms counted by `minCount n N` (odd,
with an even cyclic predecessor `C^[(j + N − 1) % N] n`). -/
def minValues (n N : ℕ) : Finset ℕ :=
  ((Finset.range N).filter (fun j => C^[j] n % 2 = 1 ∧ C^[(j + N - 1) % N] n % 2 = 0)).image (fun j => C^[j] n)

/-- At most `82` local-minimum terms in `N` steps of a cycle: fewer than `4·10^18` distinct odd values. -/
def pont_image : Prop :=
  ∀ n N : ℕ, 0 < n → 0 < N → C^[N] n = n → minCount n N ≤ 82 → (oddValues n N).card < 4 * 10 ^ 18

/-- At most `91` local-minimum terms in `N` steps of a cycle: fewer than `2·10^21` distinct odd values. -/
def pont_image_91 : Prop :=
  ∀ n N : ℕ, 0 < n → 0 < N → C^[N] n = n → minCount n N ≤ 91 → (oddValues n N).card < 2 * 10 ^ 21

/-- Over the minimal period: at most `82` distinct local-minimum values ⇒ fewer than `4·10^18` distinct odd values. -/
def pont_minimal : Prop :=
  ∀ n : ℕ, 0 < n → 0 < Function.minimalPeriod C n →
    (minValues n (Function.minimalPeriod C n)).card ≤ 82 →
    (oddValues n (Function.minimalPeriod C n)).card < 4 * 10 ^ 18

/-- Over the minimal period: at most `91` distinct local-minimum values ⇒ fewer than `2·10^21` distinct odd values. -/
def pont_minimal_91 : Prop :=
  ∀ n : ℕ, 0 < n → 0 < Function.minimalPeriod C n →
    (minValues n (Function.minimalPeriod C n)).card ≤ 91 →
    (oddValues n (Function.minimalPeriod C n)).card < 2 * 10 ^ 21

end Sdw2005
