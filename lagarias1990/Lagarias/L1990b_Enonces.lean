import Mathlib
import Lagarias.L1990_Enonces

/-!
# Lagarias 1990 · FROZEN STATEMENTS (phase 2b)

Theorems 3.1–3.2 (with NAMED hypotheses, never hidden axioms), Theorem 4.2, (2.4)–(2.5) and Table 2.1.
Written before any proof. Proofs: `Lagarias/L3b_Preuves.lean`, `Lagarias/L4b_Preuves.lean`, `Lagarias/L2b_Preuves.lean`.

## Named hypotheses

* `H_PNT` — the prime number theorem, `θ(x)/x → 1` (Chebyshev's `θ` of Mathlib). Lagarias uses it as
  `log[1,k] = k + o(k)` ([9], Theorem 434). Not in Mathlib v4.34 (it is in the PrimeNumberTheoremAnd project).
* `H_BF` — (3.3) of the paper, `|2ⁿ − 3^l| ≥ ½ n^{−c₁} 2ⁿ` for `n ≥ 2`, a consequence of the Baker–Fel'dman bound
  on linear forms in logarithms ([3], Theorem 3.1). Deep; taken as a hypothesis.

## Line-by-line comparison with the paper

| paper | Lean | deviation |
|---|---|---|
| Thm 3.1 (p. 42): infinitely many `k ≡ ±1 (6)` such that `T_k` has no primitive cycle of period `≤ (5/4)k^{1/3}` | `thm3_1` (under `H_PNT`) | the printed proof assumes that ALL `T_l`, `k0 ≤ l ≤ k`, have short primitive cycles; this includes `l` with `3 ∣ l`, which have no primitive cycle at all, so the contraposition can only produce such an `l`. Repaired: the argument is run over the primes `p ≥ 5` of `(k0, k]` (the `k` found is prime) |
| (same, unconditional) | `thm3_1_65` | constant `6/5` instead of `5/4`, with the Chebyshev bounds of Mathlib instead of the prime number theorem |
| proof of Thm 3.1: `k ∣ D(v) = 2ⁿ − 3^l`, `1 ≤ l ≤ n` | `k_dvd_D` | none |
| proof of Thm 3.1: `S(t) ≤ 3^{t(t+1)(2t+1)/6}` | `S31`, `S31_bound` | none |
| Thm 3.2 (p. 42): infinitely many `k ≡ ±1 (6)` such that every primitive cycle `v` of `T_k` has `k = D(v)/(N(v),D(v)) ≤ (log D(v))³` | `thm3_2` (under `H_BF`) | `log₂` and `|D(v)|` (the printed proof uses `log₂`; with the natural logarithm it would only give `k ≤ (log₂ e)³ (ln|D|)³`); stated for every period `p` of the cycle; obtained from `thm3_1_65`, so `H_PNT` is not needed |
| Ash, Lemma 4.7.2 (p. 49): `Σ_{j ≥ αk} C(k,j) ≤ 2^{H(α)k}`, `α ≥ ½` | `Hb`, `ash_tail` | `α ≤ 1` made explicit |
| Thm 4.2 (p. 48): `(M,6) = 1`, `M = 2^{αn}`, `α ≤ α_c = (1−H(φ))/(2−H(φ))`: `F(n,M) ≤ 2n⁴ 2^{(1−α)n}` | `thm4_2` (constant `4n⁴`), `thm4_2_printed` (constant `2n⁴`) | the printed proof ends with `4n⁴` (p. 50); `thm4_2` is what the proof gives; `α_c` is kept symbolic |
| p. 38: irreducible vectors, `I(n)` = number of irreducible cycles of length `n` | `Irred`, `Iirr` | `I(n)` = (number of irreducible words of length `n`)/`n`, as the paper says an irreducible cycle "corresponds to a set of `n` cyclic permutations" |
| (2.4) `Σ_{d∣n} d I(d) = 2ⁿ`, (2.5) Möbius inversion | `eq2_4`, `eq2_5` | none |
| Table 2.1 | `table2_1` | none |
-/

namespace Lagarias

open LaboBP LaboHH

/-! ## Named hypotheses -/

/-- The prime number theorem, `θ(x) ~ x`. -/
def H_PNT : Prop := Filter.Tendsto (fun x : ℝ => Chebyshev.theta x / x) Filter.atTop (nhds 1)

/-- (3.3): Baker–Fel'dman. -/
def H_BF : Prop :=
  ∃ c₁ : ℝ, ∀ n l : ℕ, 2 ≤ n → (1 / 2 : ℝ) * (n : ℝ) ^ (-c₁) * 2 ^ n ≤ |(2 : ℝ) ^ n - 3 ^ l|

/-! ## Theorems 3.1 and 3.2 -/

/-- `T_k` has no primitive cycle of period `≤ y`. -/
def NoShortPrimCycle (k : ℤ) (y : ℝ) : Prop :=
  ∀ (n0 : ℤ) (p : ℕ), InPrimCycle k n0 → 0 < p → (Tk k)^[p] n0 = n0 → y < p

/-- Theorem 3.1 (under the prime number theorem, as in the paper). -/
def thm3_1 : Prop :=
  H_PNT → {k : ℤ | 0 < k ∧ (k % 6 = 1 ∨ k % 6 = 5) ∧
    NoShortPrimCycle k (5 / 4 * (k : ℝ) ^ ((1 : ℝ) / 3))}.Infinite

/-- Theorem 3.1 with the constant `6/5`, without hypothesis. -/
def thm3_1_65 : Prop :=
  {k : ℤ | 0 < k ∧ (k % 6 = 1 ∨ k % 6 = 5) ∧ NoShortPrimCycle k (6 / 5 * (k : ℝ) ^ ((1 : ℝ) / 3))}.Infinite

/-- Proof of Theorem 3.1: `k ∣ 2^p − 3^l` with `1 ≤ l ≤ p`. -/
def k_dvd_D : Prop :=
  ∀ (k n0 : ℤ) (p : ℕ), 0 < k → InPrimCycle k n0 → 0 < p → (Tk k)^[p] n0 = n0 →
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ p ∧ k ∣ 2 ^ p - 3 ^ l

/-- `S(t) = ∏_{n=1}^{t} ∏_{l=1}^{n} |2ⁿ − 3^l|`. -/
def S31 (t : ℕ) : ℕ := ∏ n ∈ Finset.Icc 1 t, ∏ l ∈ Finset.Icc 1 n, ((2 : ℤ) ^ n - 3 ^ l).natAbs

/-- `S(t) ≤ 3^{t(t+1)(2t+1)/6}`. -/
def S31_bound : Prop := ∀ t : ℕ, 0 < S31 t ∧ S31 t ≤ 3 ^ (t * (t + 1) * (2 * t + 1) / 6)

/-- Theorem 3.2 (under `H_BF`). -/
def thm3_2 : Prop :=
  H_BF → {k : ℤ | 0 < k ∧ (k % 6 = 1 ∨ k % 6 = 5) ∧
    ∀ (n0 : ℤ) (p : ℕ), InPrimCycle k n0 → 0 < p → (Tk k)^[p] n0 = n0 →
      (k : ℝ) ≤ (Real.logb 2 |((d (parWord ((n0 : ℚ) / k) p) : ℤ) : ℝ)|) ^ 3}.Infinite

/-! ## Theorem 4.2 -/

/-- Binary entropy in base 2. -/
noncomputable def Hb (x : ℝ) : ℝ := -x * Real.logb 2 x - (1 - x) * Real.logb 2 (1 - x)

/-- `φ = (log₂ 3)^{−1} = log₃ 2`. -/
noncomputable def phiL : ℝ := Real.logb 3 2

/-- `α_c = (1 − H(φ)) / (2 − H(φ))`. -/
noncomputable def alphaC : ℝ := (1 - Hb phiL) / (2 - Hb phiL)

/-- [1], Lemma 4.7.2. -/
def ash_tail : Prop :=
  ∀ (k : ℕ) (a : ℝ), 1 / 2 ≤ a → a ≤ 1 →
    ∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => a * (k : ℝ) ≤ (j : ℝ)), (k.choose j : ℝ) ≤ 2 ^ (Hb a * k)

/-- Theorem 4.2, with the constant given by the printed proof (`4n⁴`); `2^{(1−α)n} = 2ⁿ/M`. -/
def thm4_2 : Prop :=
  ∀ n M : ℕ, 0 < n → 0 < M → Nat.Coprime M 6 → (M : ℝ) ≤ 2 ^ (alphaC * n) →
    ∀ r, (cntRes n M r : ℝ) * M ≤ 4 * n ^ 4 * 2 ^ n

/-- Theorem 4.2 as printed (`2n⁴`). -/
def thm4_2_printed : Prop :=
  ∀ n M : ℕ, 0 < n → 0 < M → Nat.Coprime M 6 → (M : ℝ) ≤ 2 ^ (alphaC * n) →
    ∀ r, (cntRes n M r : ℝ) * M ≤ 2 * n ^ 4 * 2 ^ n

/-! ## (2.4), (2.5), Table 2.1 -/

/-- Irreducible word: its cyclic permutations are pairwise distinct (p. 38). -/
def Irred (v : List Bool) : Prop := ∀ i ∈ Finset.Ico 1 v.length, v.rotate i ≠ v

instance (v : List Bool) : Decidable (Irred v) := by unfold Irred; infer_instance

/-- `I(n)`: the number of irreducible cycles of length `n`. -/
def Iirr (n : ℕ) : ℕ := ((words n).filter Irred).card / n

/-- (2.4). -/
def eq2_4 : Prop := ∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, d * Iirr d = 2 ^ n

/-- (2.5). -/
def eq2_5 : Prop :=
  ∀ n : ℕ, 0 < n → ((n * Iirr n : ℕ) : ℤ) = ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * 2 ^ (n / d)

/-- Table 2.1 (p. 38). -/
def table2_1 : Prop :=
  (List.range 20).map (fun i => Iirr (i + 1)) =
    [2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186, 335, 630, 1161, 2182, 4080, 7710, 14532, 27594, 52377]

end Lagarias
