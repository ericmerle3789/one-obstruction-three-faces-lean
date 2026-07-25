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

SCOPE, stated plainly. Everything below is proved: kernel-3, no `sorry`, no user axioms,
no `native_decide`. `deficit_term_le` is the analytic heart (now elementary); `key_core`
is the heart of the assembly — it absorbs the Diophantine hypothesis and the `j`-dependence.
What remains outside Lean is pure exponent bookkeeping from `key_core` + `deficit_term_le`
to the `n`-indexed statement `MarginTarget`; verified in exact integers (REQ-MATH-042,
`n = 1..300`, 0 failures), deliberately left explicit rather than hidden.
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

#print axioms deficit_term_le
#print axioms deficit_choose_le



/-! ## The three integer atoms for `MarginTarget` (s = 15, t = 86)

Verified numerically first (REQ-MATH-041, exact big-integer arithmetic, committed):
the admissible window for `t/s` is `[5.727444, 5.747075]` — width `0.0196` — and
`s = 15, t = 86` is the smallest admissible pair. Exact margins: `(A)` 0.088 bits,
`(a)` 0.327 bits, `(b)` 324 bits. The first two are razor-thin but exact.
A wrong upper bound in the first draft of the search made `(a)` fail at `s = 1`;
the failure is what exposed the bug. Recorded, not smoothed. -/

/-- Atom (A): `(19/14)^195 ≤ 2^86`, cleared of denominators. Margin 0.088 bits. -/
theorem atom_A : (19 : ℕ) ^ 195 ≤ 14 ^ 195 * 2 ^ 86 := by norm_num

/-- Atom (a): the per-`n` factor. Margin 0.327 bits. -/
theorem atom_a : (3 : ℕ) ^ 86 * 2 ^ 15 * 7 ^ 195 ≤ 12 ^ 195 := by norm_num

/-- Atom (D): the constant factor, in the `m = k + j` parametrisation. Margin ≈ 325 bits.
    (Supersedes an earlier, clumsier constant atom; the `k+j` parametrisation removes all
    natural subtraction and reduces the constant to `3^86 ≤ 2^461`.) -/
theorem atom_D : (2 : ℕ) ^ 101 * 3 ^ 86 ≤ 2 ^ 562 := by
  have h3 : (3:ℕ) ^ 86 ≤ 2 ^ 172 := by
    calc (3:ℕ) ^ 86 ≤ 4 ^ 86 := Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ 172 := by rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  calc (2:ℕ) ^ 101 * 3 ^ 86 ≤ 2 ^ 101 * 2 ^ 172 := Nat.mul_le_mul_left _ h3
    _ = 2 ^ 273 := by rw [← pow_add]
    _ ≤ 2 ^ 562 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-! ## Assembly: the heart

Parametrised as `m = k + j`, `n = k + 1`, `K = k + j + 2` — no natural subtraction.
Verified in exact integers first (REQ-MATH-042: full chain `n = 1..300`, 0 failures). -/

/-- **The core of the assembly.** Everything that depends on `j` and on the Diophantine
    hypothesis is concentrated here; the rest is bookkeeping on exponents. -/
theorem key_core (k j : ℕ) (hub : (2:ℕ) ^ (k + j + 2) ≤ 2 * 3 ^ (k + 1)) :
    2 ^ (86 * (k + j + 2)) * 2 ^ (15 * (k + 1)) * 7 ^ (195 * k)
      ≤ 2 ^ 562 * 12 ^ (195 * k) := by
  have e1 : 86 * (k + 1) = 86 + 86 * k := by ring
  have e2 : 15 * (k + 1) = 15 + 15 * k := by ring
  -- hub to the 86th power
  have h1 : (2:ℕ) ^ (86 * (k + j + 2)) ≤ 2 ^ 86 * 3 ^ (86 * (k + 1)) := by
    calc (2:ℕ) ^ (86 * (k + j + 2)) = (2 ^ (k + j + 2)) ^ 86 := by
          rw [mul_comm, pow_mul]
      _ ≤ (2 * 3 ^ (k + 1)) ^ 86 := Nat.pow_le_pow_left hub _
      _ = 2 ^ 86 * (3 ^ (k + 1)) ^ 86 := by rw [mul_pow]
      _ = 2 ^ 86 * 3 ^ (86 * (k + 1)) := by rw [← pow_mul, mul_comm (k + 1) 86]
  -- the per-k factor, via atom_a
  have h2 : (3:ℕ) ^ (86 * k) * 2 ^ (15 * k) * 7 ^ (195 * k) ≤ 12 ^ (195 * k) := by
    have hpow : (3:ℕ) ^ (86 * k) * 2 ^ (15 * k) * 7 ^ (195 * k)
        = (3 ^ 86 * 2 ^ 15 * 7 ^ 195) ^ k := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
          mul_comm 86 k, mul_comm 15 k, mul_comm 195 k]
    have h12 : (12:ℕ) ^ (195 * k) = (12 ^ 195) ^ k := by
      rw [← pow_mul, mul_comm 195 k]
    rw [hpow, h12]
    exact Nat.pow_le_pow_left atom_a k
  calc 2 ^ (86 * (k + j + 2)) * 2 ^ (15 * (k + 1)) * 7 ^ (195 * k)
      ≤ (2 ^ 86 * 3 ^ (86 * (k + 1))) * 2 ^ (15 * (k + 1)) * 7 ^ (195 * k) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ = 2 ^ 101 * 3 ^ 86 * (3 ^ (86 * k) * 2 ^ (15 * k) * 7 ^ (195 * k)) := by
        rw [e1, e2, pow_add, pow_add]; ring
    _ ≤ 2 ^ 101 * 3 ^ 86 * 12 ^ (195 * k) := Nat.mul_le_mul_left _ h2
    _ ≤ 2 ^ 562 * 12 ^ (195 * k) := Nat.mul_le_mul_right _ atom_D

#print axioms atom_A
#print axioms atom_a
#print axioms atom_D
#print axioms key_core

/-- Remaining: the bookkeeping from `key_core` + `deficit_term_le` to the `n`-indexed
    margin statement (exponent arithmetic only, no new mathematical content).
    Verified in exact integers, **not yet formalized**. -/
def MarginTarget : Prop :=
  ∀ n K : ℕ, 1 ≤ n → 3 ^ n ≤ 2 ^ K → 2 ^ K < 2 * 3 ^ n →
    ((K - 2).choose (n - 1)) ^ 13 * 2 ^ n ≤ 2 ^ (13 * K)

end DeficitLemma
