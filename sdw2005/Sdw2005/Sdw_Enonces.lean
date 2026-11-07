import Mathlib

/-!
# Sdw2005 · FROZEN STATEMENTS

Written before the proofs (committed alone). The analytic half of J. Simons and B. de Weger, *Theoretical and
computational bounds for m-cycles of the 3n + 1 problem* (Acta Arith. 117 (2005); version 1.44 of 2010 read), in the
part that bounds `K` from above, **without** their Lemma 12 (Rhin's lower bound for `|x log 2 + y log 3|`): the
a priori bound comes instead from `../logs23/` (the bridge of convergents of `log₂ 3` up to `qBr' ≈ 6.34·10^100`
and `two_log_lower`).

Layer 1 is the chain equation of their §2.1 (indices modulo `m`). Lemmas 4, 6 and 7 are theirs, in the form with
`X0 = 1` (every local minimum is `≥ 1`); with `X0 = 1` their constant `c_m` equals `2`. `chain_K_lt` is the target
of layer 1: for `m ≤ 82`, `K < 4·10^18`, without any hypothesis.

Layer 2 is the dynamics: the map `C(n) = n/2` (`n` even), `(3n + 1)/2` (`n` odd), a cycle `C^[N] n = n` on the
positive integers, `oddCount n N` odd steps and `minCount n N` local minima (odd values preceded, cyclically, by an
even one) in the `N` steps. `cycle_chain` turns a cycle into a solution of the chain equation with `m = minCount n N`
and `K = oddCount n N`; `cycle_K_lt` is the final statement.
-/

namespace Sdw2005

/-- `δ = log₂ 3`. -/
noncomputable def δ : ℝ := Real.log 3 / Real.log 2

/-! ## Layer 1: the chain equation -/

/-- The chain equation of Simons–de Weger (§2.1) with `m ≥ 1` blocks, indices modulo `m`:
`3^{k_i} a_i − 1 = 2^{k_{i+1} + l_i} a_{i+1} − 2^{l_i}`, all `k_i, l_i, a_i ≥ 1`. -/
def ChainSol (m : ℕ) (k l a : ℕ → ℕ) : Prop :=
  0 < m ∧ ∀ i < m, 0 < k i ∧ 0 < l i ∧ 0 < a i ∧
    (3 : ℤ) ^ k i * a i - 1 = 2 ^ (k ((i + 1) % m) + l i) * a ((i + 1) % m) - 2 ^ l i

/-- `K = k_0 + ⋯ + k_{m−1}` (the number of odd steps). -/
def Ksum (m : ℕ) (k : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range m, k i

/-- `L = l_0 + ⋯ + l_{m−1}` (the number of even steps). -/
def Lsum (m : ℕ) (l : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range m, l i

/-- The local minima `x_i = 2^{k_i} a_i − 1`. -/
def xm (k a : ℕ → ℕ) (i : ℕ) : ℕ := 2 ^ k i * a i - 1

/-- `Λ = (K + L) log 2 − K log 3`. -/
noncomputable def Lam (m : ℕ) (k l : ℕ → ℕ) : ℝ :=
  ((Ksum m k + Lsum m l : ℕ) : ℝ) * Real.log 2 - (Ksum m k : ℝ) * Real.log 3

/-- Lemma 4 of Simons–de Weger: `0 < Λ < Σ 1/x_i`. -/
def lemma4 : Prop :=
  ∀ (m : ℕ) (k l a : ℕ → ℕ), ChainSol m k l a →
    0 < Lam m k l ∧ Lam m k l < ∑ i ∈ Finset.range m, 1 / (xm k a i : ℝ)

/-- Lemma 6 of Simons–de Weger, without `X0`: `x_{i+1} < (x_i + 1)^δ / 2`. -/
def lemma6 : Prop :=
  ∀ (m : ℕ) (k l a : ℕ → ℕ), ChainSol m k l a → ∀ i < m,
    (xm k a ((i + 1) % m) : ℝ) < ((xm k a i : ℝ) + 1) ^ δ / 2

/-- Lemma 7 of Simons–de Weger with `X0 = 1`, for the local minima: `x_i ≥ 2^{(δ−1)K/(δ^m−1) − 1}`. -/
def lemma7_min : Prop :=
  ∀ (m : ℕ) (k l a : ℕ → ℕ), ChainSol m k l a → ∀ i < m,
    (2 : ℝ) ^ ((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1) - 1) ≤ (xm k a i : ℝ)

/-- Lemma 7 of Simons–de Weger with `X0 = 1` (`c_m = 2`): `Λ < 2m · 2^{−(δ−1)K/(δ^m−1)}`. -/
def lemma7 : Prop :=
  ∀ (m : ℕ) (k l a : ℕ → ℕ), ChainSol m k l a →
    Lam m k l < 2 * (m : ℝ) * (2 : ℝ) ^ (-((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1)))

/-- **Target of layer 1**, without hypothesis: for `m ≤ 82`, `K < 4·10^18`. -/
def chain_K_lt : Prop :=
  ∀ (m : ℕ) (k l a : ℕ → ℕ), ChainSol m k l a → m ≤ 82 → Ksum m k < 4 * 10 ^ 18

/-! ## Layer 2: cycles of the 3x+1 map -/

/-- `C(n) = n/2` for even `n`, `(3n + 1)/2` for odd `n`. -/
def C (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The number of odd values among `C^[j] n`, `j < N`. -/
def oddCount (n N : ℕ) : ℕ := ((Finset.range N).filter (fun j => C^[j] n % 2 = 1)).card

/-- The number of local minima among `C^[j] n`, `j < N`: odd values whose predecessor in the cycle,
`C^[(j + N − 1) % N] n`, is even. -/
def minCount (n N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun j => C^[j] n % 2 = 1 ∧ C^[(j + N - 1) % N] n % 2 = 0)).card

/-- A cycle of `C` on the positive integers gives a solution of the chain equation with `m` = the number of local
minima and `K` = the number of odd steps, over the same `N` steps. -/
def cycle_chain : Prop :=
  ∀ n N : ℕ, 0 < n → 0 < N → C^[N] n = n →
    ∃ k l a : ℕ → ℕ, ChainSol (minCount n N) k l a ∧ Ksum (minCount n N) k = oddCount n N

/-- **Final statement**, without hypothesis: a cycle of `C` on the positive integers with at most `82` local minima
in `N` steps has fewer than `4·10^18` odd steps in those `N` steps. -/
def cycle_K_lt : Prop :=
  ∀ n N : ℕ, 0 < n → 0 < N → C^[N] n = n → minCount n N ≤ 82 → oddCount n N < 4 * 10 ^ 18

end Sdw2005
