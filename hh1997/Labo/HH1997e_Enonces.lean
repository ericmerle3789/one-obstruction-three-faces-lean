import Mathlib
import Labo.HH1997b_Enonces

/-!
# LABO-COLLATZ · HH1997e · formaliste (2026-10-19) — FROZEN STATEMENT: the equivalence (A′) of §5

L. Halbeisen, N. Hungerbühler, Acta Arith. 78 (1997), p. 238: "Using Lemma 9 we see that ¬(A) is equivalent to
(A′) There exists a non-periodic `s ∈ S_l`, `l > 3`, such that `gcd{ϕ(t) : t ∈ σ(s)} = 2^{l(s)} − 3^{n(s)}`",
where (A) is "(1, 2) is the only Collatz cycle in ℕ" (§1).

Only definitions and `def <X> : Prop`; proof in `Labo/HH1997e_Preuves.lean`.  Reuses `phi`, `collatzQ`, `cycle`,
`LaboBP.d` (batches HH1997, HH1997b, frozen, not modified).

| paper | Lean | deviation |
|---|---|---|
| ¬(A): a Collatz cycle in ℕ other than `(1, 2)` | `notA` | a cycle in ℕ = the orbit `cycle x₀` of a positive integer `x₀` that is a periodic point of (1) |
| `s` non-periodic (not a power of a shorter word) | `NonPeriodic` | stated as "no rotation `λ^k`, `0 < k < l`, fixes `s`", the usual equivalent form (the equivalence itself is not proved here) |
| `gcd{ϕ(t) : t ∈ σ(s)} = 2^{l(s)} − 3^{n(s)}` | `Finset.gcd` over `k = 1, …, l`, as in `lemma9_15` | none |
| ¬(A) ⇔ (A′) | `Aprime_equiv` | none |
-/

namespace LaboHH

open LaboBP

/-- ¬(A): there is a Collatz cycle in ℕ other than `(1, 2)`. -/
def notA : Prop :=
  ∃ x₀ : ℕ, 0 < x₀ ∧ ((x₀ : ℚ) ∈ Function.periodicPts collatzQ) ∧ cycle (x₀ : ℚ) ≠ {1, 2}

/-- `s` is non-periodic: no rotation `λ^k`, `0 < k < l(s)`, fixes it. -/
def NonPeriodic (s : List Bool) : Prop := ∀ k, 0 < k → k < s.length → s.rotate k ≠ s

/-- (A′). -/
def Aprime : Prop :=
  ∃ s : List Bool, 3 < s.length ∧ NonPeriodic s ∧
    (Finset.range s.length).gcd (fun k => (phi (s.rotate (k + 1)) : ℤ)) = d s

/-- ¬(A) ⇔ (A′). -/
def Aprime_equiv : Prop := notA ↔ Aprime

end LaboHH
