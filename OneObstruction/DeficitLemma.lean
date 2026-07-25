/-
DeficitLemma.lean — The entropy-deficit lemma, in kernel-friendly integer form.
Session 2026-07-25, A.R.E.S. protocol (Merle side).

CONTEXT. The L-A7 ledger entry rests on the margin inequality `margin(n) ≥ c_gen·n`,
where `margin(n) = K − log₂ C(K−2, n−1)` and `K = ⌈n·log₂3⌉`. Its published-style proof
(Merle, Junction Theorem preprint 2026, §3) goes through the binary-entropy bound
`C(m,k) ≤ 2^{m·h(k/m)}`, with deficit constant `γ = 1 − h(1/log₂3)`; verified 2026-07-25
that `γ·log₂3 = c_gen` exactly (REQ-MATH-037). That route needs real analysis (entropy,
Stirling) and formalizes badly.

THIS FILE replaces the analytic core by a rational-parameter bound. For any `x > 0`,
`C(m,k)·x^k ≤ (1+x)^m` because the left side is a single term of the binomial expansion.
Choosing the rational `x = 12/7` — near the optimum `x* = 1/(log₂3 − 1) ≈ 1.7095` — and
clearing denominators gives a statement in ℕ with **no** real analysis, and `19 = 12 + 7`
makes it literally "one summand ≤ the sum".

Numerically established before formalizing (REQ-MATH-039/040, canary-anchored, committed):
* the resulting asymptotic constant is `0.0793165`, within `2.1·10⁻⁶` of `c_gen`;
* with the safe rational `c = 1/13`, `margin(n) ≥ n/13` holds for `n = 1..3000`,
  0 failures, minimum slack `1.700` bits at `n = 12`;
* the integer target `C(K−2,n−1)^13 · 2^n ≤ 2^{13K}` holds for `n = 1..1200`,
  0 failures, and the binomial route below implies it with ≥ 22 bits to spare.

SCOPE, stated plainly. `deficit_term_le` below is proved, kernel-3, 0 sorry — it is the
analytic heart, and it is now elementary. The passage from it to the `n`-indexed statement
additionally needs the comparison between `K` and `n` (`3^n ≤ 2^K < 2·3^n`); that step is
stated here as `MarginTarget` and is **not yet proved in Lean** — it is a finite-rational
exponent comparison, deliberately left explicit rather than hidden.
-/
import Mathlib

namespace DeficitLemma

/-- **The deficit lemma, integer form.** `C(m,k)·12^k·7^(m−k) ≤ 19^m` for `k ≤ m`.
    Proof: `19 = 12 + 7`, and the left-hand side is a single summand of `(12+7)^m`. -/
theorem deficit_term_le (m k : ℕ) (h : k ≤ m) :
    12 ^ k * 7 ^ (m - k) * (m.choose k) ≤ 19 ^ m := by
  have h19 : (19 : ℕ) = 12 + 7 := by norm_num
  rw [h19, add_pow]
  exact Finset.single_le_sum
    (f := fun j => 12 ^ j * 7 ^ (m - j) * (m.choose j))
    (fun i _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

/-- Same bound, written with the binomial coefficient first (convenience form). -/
theorem deficit_choose_le (m k : ℕ) (h : k ≤ m) :
    (m.choose k) * (12 ^ k * 7 ^ (m - k)) ≤ 19 ^ m := by
  have := deficit_term_le m k h
  calc (m.choose k) * (12 ^ k * 7 ^ (m - k))
      = 12 ^ k * 7 ^ (m - k) * (m.choose k) := by ring
    _ ≤ 19 ^ m := this

/- Non-vacuity canaries (kernel reduction + `norm_num`; no `native_decide`). -/

/-- Canary 1: the theorem instantiated — a genuine instance, not a restatement. -/
example : 12 ^ 4 * 7 ^ 6 * (Nat.choose 10 4) ≤ 19 ^ 10 :=
  deficit_term_le 10 4 (by norm_num)

/-- Canary 2: the binomial coefficient really is what we think (kernel-evaluated). -/
example : Nat.choose 10 4 = 210 := by rfl

/-- Canary 3: the inequality is not vacuous — both sides computed, gap real. -/
example : 12 ^ 4 * 7 ^ 6 * 210 < 19 ^ 10 := by norm_num

/-- Canary 4: a larger instance, tight regime (k/m ≈ 1/log₂3). -/
example : 12 ^ 10 * 7 ^ 15 * (Nat.choose 25 10) ≤ 19 ^ 25 :=
  deficit_term_le 25 10 (by norm_num)

/-- Canary 5: the edge case k = m (single term = last term). -/
example : 12 ^ 7 * 7 ^ 0 * (Nat.choose 7 7) ≤ 19 ^ 7 :=
  deficit_term_le 7 7 (le_refl 7)

/-- The `K`-vs-`n` comparison that turns `deficit_term_le` into the ledger's margin
    statement. `K` is the least exponent with `3^n ≤ 2^K`. Verified numerically for
    `n = 1..1200` (REQ-MATH-040, 0 failures, ≥ 22 bits of slack); **not proved here**. -/
def MarginTarget : Prop :=
  ∀ n K : ℕ, 1 ≤ n → 3 ^ n ≤ 2 ^ K → 2 ^ K < 2 * 3 ^ n →
    ((K - 2).choose (n - 1)) ^ 13 * 2 ^ n ≤ 2 ^ (13 * K)

#print axioms deficit_term_le
#print axioms deficit_choose_le

end DeficitLemma
