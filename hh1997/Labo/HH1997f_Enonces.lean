import Mathlib
import Labo.HH1997c_Enonces

/-!
# LABO-COLLATZ · HH1997f · formaliste (2026-10-19) — FROZEN STATEMENTS (the finite check of §4.4)

L. Halbeisen, N. Hungerbühler, *Optimal bounds for the length of rational Collatz cycles*,
Acta Arith. 78 (1997) 227–239, §4.4 (read at source: `LABO-COLLATZ/calculs/bibliothecaire/s6src/hh1997.txt`, p. 237).
Target: `example44_check` of the frozen batch `HH1997c_Enonces` (sha256 ea5dfcd3…, NOT modified):
`Q4(l) < m = 212 366 032 807 211` for `1 ≤ l < 102 225 496`; with `example44_reduction_thm` it gives `example44`.

This file contains ONLY definitions and `def <X> : Prop` statements.  Proofs: `Labo/HH1997f_Preuves.lean`.
Reuses `phi`, `stilde`, `cl`, `M`, `nOf`, `Q4`, `Lm` (batches a, b), not redefined.

Index convention.  The paper numbers the convergents of `log₂ 3` from 1, Mathlib from 0:
paper `p₁₄ = 301 994` = Mathlib `p₁₃`, paper `p₁₆ = 17 087 915` = Mathlib `p₁₅` (`q₁₅ = 10 781 274`),
paper `p₁₇ = 85 137 581` = Mathlib `p₁₆`, and the paper's `p₁₈ = 102 225 496` is the intermediate fraction
`p₁₅ + p₁₆` (not a convergent).  Below, numbers are written out.

## Line-by-line comparison with the paper (statements frozen BEFORE any proof)

| paper (§4.4) | Lean | deviation |
|---|---|---|
| Second step: `(n(l)/l)·1/(2 − 3^{n(l)/l}) < m` for `l ∈ {p₁₆, …, p₁₈ − 1} \ (A₁ ∪ A₂)`, `A₁ = {k p₁₆ : k = 1..5}`, `A₂ = {k p₁₆ + p₁₄ : k = 3,4,5}` ("a simple Mathematica procedure") | `example44_step2` | none (ℝ, `rpow`) |
| (not printed) the same with a smaller exceptional set and for all `l ≥ 1`, in integers: `2m·3^{n(l)} < (2m − n(l))·2^l` for `1 ≤ l < p₁₈`, `l ∉ A₁ ∪ {5p₁₆ + p₁₄}` | `example44_step2_star` | stronger: 6 exceptions instead of 8, and `l < p₁₆` included (the paper's First step only bounds cycle lengths, not `Q4`) |
| Third step: `M_{l,n}/(2^l − 3^n) < m` for `l = p₁₆`, `n = n(l)` ("direct computation", Corollary 1) | `example44_step3` | none (`Q4` = Corollary 1's quotient) |
| Third step: `M_{kq₁₆,n(kq₁₆)}/(2^{kq₁₆} − 3^{n(kq₁₆)}) = M_{q₁₆,n(q₁₆)}/(2^{q₁₆} − 3^{n(q₁₆)})` "for k = 1..100", "the sequence s̃ for `l = kq₁₆` is the concatenation of `k` copies" (the paper writes `q₁₆` for `p₁₆`) | `stilde_wpow` (concatenation, any `k`, any `l, n`), `example44_A` | the copies are stated for all `k` and all `(l,n)`; `example44_A` covers `A₁ ∪ A₂` ("similar argument or direct verification") |
| (not printed) the "similar argument": (4) makes `ϕ/(2^l − 3^n) < m` stable under concatenation | `phi_lt_append` | none |
| (not printed) the factorization behind "direct computation": `s̃(l₁+l₂, n₁+n₂) = s̃(l₁,n₁) s̃(l₂,n₂)` when `n₁l₂ − n₂l₁ = 1` (Christoffel words) | `stilde_append` | none |
| "(according to Lemma 1 or Remark 1)" — read Prop. 1 (batch c, coquille 6) — at `n = n(l)`, with Bernoulli: `M_{l,n(l)} ≤ n(l)·2^{l−1}` | `M_half` | not printed; it is the form in which the Second step is proved |
| Fourth step: `Q4(l) < m` for all `l ∈ {1, …, p₁₈ − 1}` | `example44_check` (batch c, frozen) | none |
| the example: `L = 102 225 496` | `example44` (batch c, frozen) | none |
| (not printed) optimality of the example: `L(m) = p₁₈` exactly | `example44_Lm` | not claimed in the paper |
-/

namespace LaboHH

open LaboBP

/-- `w^k`: the concatenation of `k` copies of `w`. -/
def wpow (w : List Bool) (k : ℕ) : List Bool := (List.replicate k w).flatten

/-- Christoffel factorization of `s̃`: if `n₁l₂ − n₂l₁ = 1` then `s̃(l₁+l₂, n₁+n₂) = s̃(l₁,n₁) s̃(l₂,n₂)`. -/
def stilde_append : Prop :=
  ∀ l₁ n₁ l₂ n₂ : ℕ, 0 < l₁ → 0 < l₂ → n₁ * l₂ = n₂ * l₁ + 1 →
    stilde (l₁ + l₂) (n₁ + n₂) = stilde l₁ n₁ ++ stilde l₂ n₂

/-- Third step, the copies: `s̃(kl, kn) = s̃(l,n)^k`. -/
def stilde_wpow : Prop := ∀ k l n : ℕ, 0 < l → stilde (k * l) (k * n) = wpow (stilde l n) k

/-- (4) makes `ϕ(w) < B (2^{l(w)} − 3^{n(w)})` stable under concatenation. -/
def phi_lt_append : Prop :=
  ∀ (B : ℚ) (u v : List Bool),
    (phi u : ℚ) < B * ((2 : ℚ) ^ u.length - 3 ^ u.count true) →
    (phi v : ℚ) < B * ((2 : ℚ) ^ v.length - 3 ^ v.count true) →
    (phi (u ++ v) : ℚ) < B * ((2 : ℚ) ^ (u ++ v).length - 3 ^ (u ++ v).count true)

/-- Prop. 1 at `n = n(l)` with Bernoulli: `M_{l,n(l)} ≤ n(l)·2^{l−1}`. -/
def M_half : Prop := ∀ l : ℕ, 0 < l → 2 * M l (nOf l) ≤ nOf l * 2 ^ l

/-- The paper's exceptional sets `A₁ ∪ A₂` (Second step). -/
def A12 : Finset ℕ :=
  {17087915, 34175830, 51263745, 68351660, 85439575, 51565739, 68653654, 85741569}

/-- The exceptional set that is really needed: `A₁ ∪ {5p₁₆ + p₁₄}`. -/
def A6 : Finset ℕ := {17087915, 34175830, 51263745, 68351660, 85439575, 85741569}

/-- Second step, as printed. -/
def example44_step2 : Prop :=
  ∀ l : ℕ, 17087915 ≤ l → l < 102225496 → l ∉ A12 →
    (nOf l : ℝ) / l * (1 / (2 - (3 : ℝ) ^ ((nOf l : ℝ) / l))) < 212366032807211

/-- Second step, stronger and in integers: `2m·3^{n(l)} < (2m − n(l))·2^l` for `1 ≤ l < p₁₈`, `l ∉ A6`. -/
def example44_step2_star : Prop :=
  ∀ l : ℕ, 1 ≤ l → l < 102225496 → l ∉ A6 →
    2 * 212366032807211 * 3 ^ nOf l < (2 * 212366032807211 - nOf l) * 2 ^ l

/-- Third step: `Q4(p₁₆) < m` (`p₁₆ = 17 087 915`, paper's index). -/
def example44_step3 : Prop := Q4 17087915 < 212366032807211

/-- Third step, the exceptional lengths `A₁ ∪ A₂`. -/
def example44_A : Prop := ∀ l ∈ A12, Q4 l < 212366032807211

/-- Optimality of the example: the smallest `L` with `Q4(L) ≥ m` is `p₁₈ = 102 225 496`. -/
def example44_Lm : Prop := Lm 212366032807211 = 102225496

end LaboHH
