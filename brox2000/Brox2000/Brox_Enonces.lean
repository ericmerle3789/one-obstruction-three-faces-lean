import Mathlib
import Sdw2005.Sdw_Enonces
import Sdw2005.Pont_Enonces

/-!
# Brox 2000 · FROZEN STATEMENTS, phase A: cycles on the positive integers

T. Brox, *Collatz cycles with few descents*, Acta Arith. 92 (2000), 181–188.

Written before the proofs (committed alone). Brox works with `T₁(x) = (3x + 1)/2^{k(x)}` on the odd integers, where
`2^{k(x)} ∥ 3x + 1`; a Collatz cycle `Γ` is a cycle of `T₁`, `|Γ|` its number of elements, an element `x` is
*descending* if `k(x) ≥ 2`, and `δ(Γ)` is the number of descending elements. As he notes (p. 181), the Collatz cycles
are exactly the sets of odd elements of the cycles of `T(x) = x/2` (`x` even), `(3x + 1)/2` (`x` odd); and an odd `x`
is descending if and only if `T(x)` is even (`4 ∣ 3x + 1`). The statements below use `T = Sdw2005.C` on `ℕ`:

* `Gamma n`: the odd values of the cycle of `n` (`n > 0` periodic under `C`), i.e. Brox's `Γ`;
* `descSet n`: the `x ∈ Gamma n` with `C x` even, so `(descSet n).card = δ(Γ)`.

Phase A covers the cycles on the **positive** integers only; Brox's theorems also cover the cycles on the negative
integers, which are not treated here. "log" is the natural logarithm (Brox's `γ = 1 − 2 log θ = 0.0788…`).
-/

namespace Brox2000

open Sdw2005

/-- Brox's `Γ` for the cycle of `n`: the distinct odd values `C^[j] n`, `j < minimalPeriod C n`. -/
noncomputable def Gamma (n : ℕ) : Finset ℕ := oddValues n (Function.minimalPeriod C n)

/-- The descending elements of `Γ`: those `x` with `C x` even. `(descSet n).card` is Brox's `δ(Γ)`. -/
noncomputable def descSet (n : ℕ) : Finset ℕ := (Gamma n).filter (fun x => C x % 2 = 0)

/-- Lemma 2.2 (first part, `k ≤ 2n`): the period of `T` on a positive cycle is at most `2 |Γ|`. -/
def lemma22_pos : Prop :=
  ∀ n : ℕ, 0 < n → 0 < Function.minimalPeriod C n → Function.minimalPeriod C n ≤ 2 * (Gamma n).card

/-- Lemma 2.2 (second part), in the form used: for every `K`, only finitely many positive integers lie on a cycle
with `|Γ| ≤ K`. -/
def lemma22_finite_pos : Prop :=
  ∀ K : ℕ, Set.Finite {n : ℕ | 0 < n ∧ 0 < Function.minimalPeriod C n ∧ (Gamma n).card ≤ K}

/-- Theorem 1.1, explicit form (ours, for positive cycles): `δ(Γ) < 2 log |Γ|` implies `|Γ| < 2^1500`. -/
def thm11_pos_explicit : Prop :=
  ∀ n : ℕ, 0 < n → 0 < Function.minimalPeriod C n →
    ((descSet n).card : ℝ) < 2 * Real.log ((Gamma n).card : ℝ) → (Gamma n).card < 2 ^ 1500

/-- **Theorem 1.1** (positive cycles): only finitely many positive integers lie on a cycle with `δ(Γ) < 2 log |Γ|`. -/
def thm11_pos : Prop :=
  Set.Finite {n : ℕ | 0 < n ∧ 0 < Function.minimalPeriod C n ∧
    ((descSet n).card : ℝ) < 2 * Real.log ((Gamma n).card : ℝ)}

/-- **Corollary 1.2** (positive cycles): for every `ν`, only finitely many positive integers lie on a cycle with
`δ(Γ) ≤ ν`. -/
def cor12_pos : Prop :=
  ∀ ν : ℕ, Set.Finite {n : ℕ | 0 < n ∧ 0 < Function.minimalPeriod C n ∧ (descSet n).card ≤ ν}

end Brox2000
