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

/-- `key_core` with the constant `2^172` divided out. -/
theorem key_shifted (k j : ℕ) (hub : (2:ℕ) ^ (k + j + 2) ≤ 2 * 3 ^ (k + 1)) :
    2 ^ (86 * (k + j)) * 2 ^ (15 * (k + 1)) * 7 ^ (195 * k)
      ≤ 2 ^ 390 * 12 ^ (195 * k) := by
  have h := key_core k j hub
  have e : 86 * (k + j + 2) = 86 * (k + j) + 172 := by ring
  rw [e, pow_add] at h
  have e562 : (2:ℕ) ^ 562 = 2 ^ 172 * 2 ^ 390 := by rw [← pow_add]
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (2:ℕ) ^ 172 by positivity)
  calc (2:ℕ) ^ 172 * (2 ^ (86 * (k + j)) * 2 ^ (15 * (k + 1)) * 7 ^ (195 * k))
      = 2 ^ (86 * (k + j)) * 2 ^ 172 * 2 ^ (15 * (k + 1)) * 7 ^ (195 * k) := by ring
    _ ≤ 2 ^ 562 * 12 ^ (195 * k) := h
    _ = 2 ^ 172 * (2 ^ 390 * 12 ^ (195 * k)) := by rw [e562, mul_assoc]

/-- The 15th-power form of the key exponential inequality. -/
theorem key15 (k j : ℕ) (hub : (2:ℕ) ^ (k + j + 2) ≤ 2 * 3 ^ (k + 1)) :
    19 ^ (195 * (k + j)) * 2 ^ (15 * (k + 1))
      ≤ 2 ^ (195 * (k + j + 2)) * (12 ^ (195 * k) * 7 ^ (195 * j)) := by
  have hA : (19:ℕ) ^ (195 * (k + j)) ≤ 2 ^ (281 * (k + j)) * 7 ^ (195 * (k + j)) := by
    have h1 : (19:ℕ) ^ 195 ≤ 2 ^ 281 * 7 ^ 195 := by
      calc (19:ℕ) ^ 195 ≤ 14 ^ 195 * 2 ^ 86 := atom_A
        _ = (2 * 7) ^ 195 * 2 ^ 86 := by norm_num
        _ = 2 ^ 195 * 7 ^ 195 * 2 ^ 86 := by rw [mul_pow]
        _ = 2 ^ 281 * 7 ^ 195 := by rw [show (281:ℕ) = 195 + 86 by norm_num, pow_add]; ring
    calc (19:ℕ) ^ (195 * (k + j)) = (19 ^ 195) ^ (k + j) := by
          rw [← pow_mul, mul_comm 195 (k + j)]
      _ ≤ (2 ^ 281 * 7 ^ 195) ^ (k + j) := Nat.pow_le_pow_left h1 _
      _ = 2 ^ (281 * (k + j)) * 7 ^ (195 * (k + j)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
  have hs := key_shifted k j hub
  have esplit : (195:ℕ) * (k + j) = 195 * k + 195 * j := by ring
  have e281 : 281 * (k + j) = 195 * (k + j) + 86 * (k + j) := by ring
  have e195 : 195 * (k + j + 2) = 195 * (k + j) + 390 := by ring
  calc 19 ^ (195 * (k + j)) * 2 ^ (15 * (k + 1))
      ≤ (2 ^ (281 * (k + j)) * 7 ^ (195 * (k + j))) * 2 ^ (15 * (k + 1)) :=
        Nat.mul_le_mul_right _ hA
    _ = 2 ^ (195 * (k + j)) * 7 ^ (195 * j) *
          (2 ^ (86 * (k + j)) * 2 ^ (15 * (k + 1)) * 7 ^ (195 * k)) := by
        rw [e281, esplit, pow_add, pow_add]; ring
    _ ≤ 2 ^ (195 * (k + j)) * 7 ^ (195 * j) * (2 ^ 390 * 12 ^ (195 * k)) :=
        Nat.mul_le_mul_left _ hs
    _ = 2 ^ (195 * (k + j + 2)) * (12 ^ (195 * k) * 7 ^ (195 * j)) := by
        rw [e195, pow_add]; ring

/-- **The margin inequality, `(k, j)` form.** No natural subtraction, no hypothesis beyond
    the Diophantine upper bound. This is `MarginTarget` after the substitution
    `m = k + j`, `n = k + 1`, `K = k + j + 2`. -/
theorem margin_core (k j : ℕ) (hub : (2:ℕ) ^ (k + j + 2) ≤ 2 * 3 ^ (k + 1)) :
    ((k + j).choose k) ^ 13 * 2 ^ (k + 1) ≤ 2 ^ (13 * (k + j + 2)) := by
  set C := (k + j).choose k with hC
  -- the deficit lemma, with (k+j) - k = j
  have hd : 12 ^ k * 7 ^ j * C ≤ 19 ^ (k + j) := by
    have h := deficit_term_le (k + j) k (Nat.le_add_right k j)
    simpa using h
  -- raise it to the 195th power
  have hd195 : (12 ^ (195 * k) * 7 ^ (195 * j)) * C ^ 195 ≤ 19 ^ (195 * (k + j)) := by
    have := Nat.pow_le_pow_left hd 195
    calc (12 ^ (195 * k) * 7 ^ (195 * j)) * C ^ 195
        = (12 ^ k * 7 ^ j * C) ^ 195 := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k 195, mul_comm j 195]
      _ ≤ (19 ^ (k + j)) ^ 195 := this
      _ = 19 ^ (195 * (k + j)) := by rw [← pow_mul, mul_comm (k + j) 195]
  -- combine with key15 to get the 15th power of the goal
  have h15 : (C ^ 13 * 2 ^ (k + 1)) ^ 15 ≤ (2 ^ (13 * (k + j + 2))) ^ 15 := by
    have hgoal : C ^ 195 * 2 ^ (15 * (k + 1)) ≤ 2 ^ (195 * (k + j + 2)) := by
      refine Nat.le_of_mul_le_mul_left ?_
        (show 0 < 12 ^ (195 * k) * 7 ^ (195 * j) by positivity)
      calc (12 ^ (195 * k) * 7 ^ (195 * j)) * (C ^ 195 * 2 ^ (15 * (k + 1)))
          = ((12 ^ (195 * k) * 7 ^ (195 * j)) * C ^ 195) * 2 ^ (15 * (k + 1)) := by ring
        _ ≤ 19 ^ (195 * (k + j)) * 2 ^ (15 * (k + 1)) := Nat.mul_le_mul_right _ hd195
        _ ≤ 2 ^ (195 * (k + j + 2)) * (12 ^ (195 * k) * 7 ^ (195 * j)) := key15 k j hub
        _ = (12 ^ (195 * k) * 7 ^ (195 * j)) * 2 ^ (195 * (k + j + 2)) := by ring
    calc (C ^ 13 * 2 ^ (k + 1)) ^ 15
        = C ^ 195 * 2 ^ (15 * (k + 1)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k + 1) 15]
      _ ≤ 2 ^ (195 * (k + j + 2)) := hgoal
      _ = (2 ^ (13 * (k + j + 2))) ^ 15 := by
          rw [← pow_mul]; congr 1; ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h15

/-- **`MarginTarget`, proved.** The `n`-indexed form used by the L-A7 ledger entry. -/
theorem marginTarget (n K : ℕ) (hn : 1 ≤ n) (hlb : 3 ^ n ≤ 2 ^ K) (hub : 2 ^ K < 2 * 3 ^ n) :
    ((K - 2).choose (n - 1)) ^ 13 * 2 ^ n ≤ 2 ^ (13 * K) := by
  -- from 2^n < 3^n ≤ 2^K we get K ≥ n + 1, so K = (n-1) + j + 2 for some j
  have h2n : (2:ℕ) ^ n < 3 ^ n := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hKn : n + 1 ≤ K := by
    have : (2:ℕ) ^ n < 2 ^ K := lt_of_lt_of_le h2n hlb
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp this
    omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, K = k + j + 2 := ⟨K - k - 2, by omega⟩
  have hub' : (2:ℕ) ^ (k + j + 2) ≤ 2 * 3 ^ (k + 1) := le_of_lt hub
  simpa using margin_core k j hub'

#print axioms margin_core
#print axioms marginTarget

end DeficitLemma
