import Mathlib

/-!
# Brox 2000 · FROZEN STATEMENTS, phase B: all Collatz cycles, on `ℤ`

T. Brox, *Collatz cycles with few descents*, Acta Arith. 92 (2000), 181–188.

Written before the proofs (committed alone). Brox's own setting: `T : ℤ → ℤ`, `T(x) = x/2` (`x` even),
`(3x + 1)/2` (`x` odd) (p. 181). A Collatz cycle is a cycle of `T₁` on the odd integers, i.e. the set of odd elements of
a cycle of `T` (p. 181), positive or negative; `|Γ|` is its number of elements, `δ(Γ)` the number of its descending
elements (`k(x) ≥ 2`, i.e. `4 ∣ 3x + 1`, i.e. `T x` even). The cycle `{0}` of `T` has no odd element and is not a
Collatz cycle.

* `GammaZ x`: the odd values `T^[j] x`, `j < minimalPeriod T x` (Brox's `Γ` when `x` lies on a cycle of `T`);
* `descSetZ x`: the `y ∈ GammaZ x` with `T y` even, so `(descSetZ x).card = δ(Γ)`.

On `ℤ`, `x % 2` is `0` or `1` (Euclidean remainder) and `(3x + 1)/2` is exact for `x` odd. "log" is the natural
logarithm. Phase A (`Brox2000/Brox_Enonces.lean`) states the same results on `ℕ` for the positive cycles.
-/

namespace Brox2000

/-- Brox's `T` on `ℤ`. -/
def T (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- Brox's `Γ` for the cycle of `x`: the distinct odd values `T^[j] x`, `j < minimalPeriod T x`. -/
noncomputable def GammaZ (x : ℤ) : Finset ℤ :=
  ((Finset.range (Function.minimalPeriod T x)).image (fun j => T^[j] x)).filter (fun y => y % 2 = 1)

/-- The descending elements of `Γ`: those `y` with `T y` even. `(descSetZ x).card` is Brox's `δ(Γ)`. -/
noncomputable def descSetZ (x : ℤ) : Finset ℤ := (GammaZ x).filter (fun y => T y % 2 = 0)

/-- Lemma 2.2 (first part, `k ≤ 2n`), on `ℤ`: the period of `T` on a cycle other than `{0}` is at most `2 |Γ|`. -/
def lemma22_Z : Prop :=
  ∀ x : ℤ, x ≠ 0 → 0 < Function.minimalPeriod T x → Function.minimalPeriod T x ≤ 2 * (GammaZ x).card

/-- Lemma 2.2 (second part), on `ℤ`: for every `K`, only finitely many integers lie on a cycle of `T` with
`|Γ| ≤ K`. -/
def lemma22_finite_Z : Prop :=
  ∀ K : ℕ, Set.Finite {x : ℤ | 0 < Function.minimalPeriod T x ∧ (GammaZ x).card ≤ K}

/-- Theorem 1.1, explicit form (ours), on `ℤ`: `δ(Γ) < 2 log |Γ|` implies `|Γ| < 2^1500`. -/
def thm11_Z_explicit : Prop :=
  ∀ x : ℤ, 0 < Function.minimalPeriod T x →
    ((descSetZ x).card : ℝ) < 2 * Real.log ((GammaZ x).card : ℝ) → (GammaZ x).card < 2 ^ 1500

/-- **Theorem 1.1**: only finitely many integers lie on a cycle of `T` with `δ(Γ) < 2 log |Γ|`. -/
def thm11_Z : Prop :=
  Set.Finite {x : ℤ | 0 < Function.minimalPeriod T x ∧
    ((descSetZ x).card : ℝ) < 2 * Real.log ((GammaZ x).card : ℝ)}

/-- **Corollary 1.2**: for every `ν`, only finitely many integers lie on a cycle of `T` with `δ(Γ) ≤ ν`. -/
def cor12_Z : Prop :=
  ∀ ν : ℕ, Set.Finite {x : ℤ | 0 < Function.minimalPeriod T x ∧ (descSetZ x).card ≤ ν}

end Brox2000
