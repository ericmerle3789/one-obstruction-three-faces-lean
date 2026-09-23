/-
  L-A1 : The transport recurrence and the divisibility collapse
  =============================================================

  Joint result — independent simultaneous discovery:
    * E. Merle    : integer form  (correspondence 2026-07-18)
    * B. Macindoe : fixed-point form (reverse.md 14.15.9.2, merged 2026-07-17)
  joined by the seam identity  N_r + q = 2^{m_r} R_r.

  This Lean artifact (Merle side, the "kernel key") certifies the
  KERNEL-FRIENDLY CORE:  from the transport recurrence, the p per-rotation
  divisibility conditions  q | R_r  of a period-p Collatz cycle collapse to
  a SINGLE condition  q | R_0.

  Scope, stated ARES-honestly:
   * PROVEN HERE (kernel, 0 `sorry`): recurrence  ⟹  (q | R r ↔ q | R 0),
     for the UNREDUCED modulus  q = 2^K − 3^n.
   * NOT proven here (established elsewhere): that the elimination numerators
     R_r satisfy the recurrence — an algebraic identity verified numerically
     on both sides (29,211 checks + 60 shared test-vectors, 0 failures) and
     proved in fixed-point form in Macindoe, reverse.md 14.15.9.2.

  The modulus is the UNREDUCED  q = 2^K − 3^n.  It differs from the reduced
  denominator exactly when  gcd(q, R_r) > 1  (e.g. the p=7 seed n=94 has
  gcd = 7 at every rotation); unit transport mod the unreduced q implies it
  mod every divisor, so this is the right modulus to formalize.
-/
import Mathlib

namespace CollatzTransport

/-- **Abstract collapse.**  Along a transport chain
    `U r * R (r+1) = V r * R r + C r * q`,
    where each `U r` and `V r` is coprime to `q`, divisibility by `q`
    is invariant along the chain: `q ∣ R r ↔ q ∣ R 0` for every `r`. -/
theorem collapse_of_recurrence
    (q : ℤ) (R U V C : ℕ → ℤ)
    (hU : ∀ r, IsCoprime q (U r)) (hV : ∀ r, IsCoprime q (V r))
    (hrec : ∀ r, U r * R (r + 1) = V r * R r + C r * q) :
    ∀ r, (q ∣ R r ↔ q ∣ R 0) := by
  have step : ∀ r, (q ∣ R r ↔ q ∣ R (r + 1)) := by
    intro r
    have hV' : q ∣ V r * R r ↔ q ∣ R r :=
      ⟨fun h => (hV r).dvd_of_dvd_mul_left h, fun h => h.mul_left (V r)⟩
    have hU' : q ∣ U r * R (r + 1) ↔ q ∣ R (r + 1) :=
      ⟨fun h => (hU r).dvd_of_dvd_mul_left h, fun h => h.mul_left (U r)⟩
    have hmid : q ∣ U r * R (r + 1) ↔ q ∣ V r * R r := by
      rw [hrec r]; exact dvd_add_left (dvd_mul_left q (C r))
    exact hV'.symm.trans (hmid.symm.trans hU')
  intro r
  induction r with
  | zero => exact Iff.rfl
  | succ k ih => exact (step k).symm.trans ih

/-- `2 ∤ (2^K − 3^n)` for `K ≥ 1`. -/
theorem two_not_dvd_q {K n : ℕ} (hK : K ≠ 0) : ¬ (2 : ℤ) ∣ (2 ^ K - 3 ^ n) := by
  intro hdvd
  have h2K : (2 : ℤ) ∣ 2 ^ K := dvd_pow_self 2 hK
  have h3n : (2 : ℤ) ∣ 3 ^ n := by
    have := dvd_sub h2K hdvd
    simpa using this
  have : (2 : ℤ) ∣ 3 := (Int.prime_two).dvd_of_dvd_pow h3n
  norm_num at this

/-- `3 ∤ (2^K − 3^n)` for `n ≥ 1`. -/
theorem three_not_dvd_q {K n : ℕ} (hn : n ≠ 0) : ¬ (3 : ℤ) ∣ (2 ^ K - 3 ^ n) := by
  intro hdvd
  have h3n : (3 : ℤ) ∣ 3 ^ n := dvd_pow_self 3 hn
  have h2K : (3 : ℤ) ∣ 2 ^ K := by
    have := dvd_add hdvd h3n
    simpa using this
  have : (3 : ℤ) ∣ 2 := (Int.prime_three).dvd_of_dvd_pow h2K
  norm_num at this

/-- `q = 2^K − 3^n` is coprime to every power of 2 (for `K ≥ 1`). -/
theorem coprime_pow_two {K n : ℕ} (hK : K ≠ 0) (e : ℕ) :
    IsCoprime ((2 : ℤ) ^ K - 3 ^ n) (2 ^ e) :=
  (((Int.prime_two).coprime_iff_not_dvd.mpr (two_not_dvd_q hK)).symm).pow_right

/-- `q = 2^K − 3^n` is coprime to every power of 3 (for `n ≥ 1`). -/
theorem coprime_pow_three {K n : ℕ} (hn : n ≠ 0) (e : ℕ) :
    IsCoprime ((2 : ℤ) ^ K - 3 ^ n) (3 ^ e) :=
  (((Int.prime_three).coprime_iff_not_dvd.mpr (three_not_dvd_q hn)).symm).pow_right

/-- **A1 (transport collapse), unreduced modulus.**
    For `q = 2^K − 3^n` (`K, n ≥ 1`) and rotation numerators `R` satisfying
    the transport recurrence with exponents `σ, m, s`, the `p` divisibility
    conditions collapse to one: `q ∣ R r ↔ q ∣ R 0` for every rotation `r`. -/
theorem transport_collapse
    (K n : ℕ) (hK : K ≠ 0) (hn : n ≠ 0)
    (R : ℕ → ℤ) (σ m s : ℕ → ℕ)
    (hrec : ∀ r, (2 : ℤ) ^ (σ r) * R (r + 1)
                 = 3 ^ (m r) * R r + (2 ^ (s r) - 1) * (2 ^ K - 3 ^ n)) :
    ∀ r, ((2 ^ K - 3 ^ n : ℤ) ∣ R r ↔ (2 ^ K - 3 ^ n : ℤ) ∣ R 0) :=
  collapse_of_recurrence (2 ^ K - 3 ^ n) R
    (fun r => 2 ^ (σ r)) (fun r => 3 ^ (m r)) (fun r => 2 ^ (s r) - 1)
    (fun r => coprime_pow_two hK (σ r)) (fun r => coprime_pow_three hn (m r))
    hrec

/-- **The headline (A1).**  The whole period-`p` divisibility system is
    equivalent to a *single* check: verifying `q ∣ R 0` alone certifies
    `q ∣ R r` for every rotation `r`.  This is the "`p` conditions are one
    condition" statement of ledger entry L-A1. -/
theorem cycle_divisibility_one_check
    (K n : ℕ) (hK : K ≠ 0) (hn : n ≠ 0)
    (R : ℕ → ℤ) (σ m s : ℕ → ℕ)
    (hrec : ∀ r, (2 : ℤ) ^ (σ r) * R (r + 1)
                 = 3 ^ (m r) * R r + (2 ^ (s r) - 1) * (2 ^ K - 3 ^ n)) :
    (∀ r, (2 ^ K - 3 ^ n : ℤ) ∣ R r) ↔ (2 ^ K - 3 ^ n : ℤ) ∣ R 0 := by
  constructor
  · intro h; exact h 0
  · intro h r; exact (transport_collapse K n hK hn R σ m s hrec r).mpr h

/-- **ARES sanity canary.**  The recurrence hypothesis is *non-vacuous*: the
    trivial cycle (`p = 2`, `K = 4`, `n = 2`, so `q = 2^4 − 3^2 = 7` and every
    `R_r = q = 7`) satisfies it — `2^2·7 = 3·7 + (2−1)·7`, i.e. `28 = 28`.
    A theorem proved from a contradictory hypothesis would be worthless; this
    exhibits a genuine model, so the collapse has content. -/
example : ∀ r : ℕ, ((2 : ℤ) ^ 4 - 3 ^ 2) ∣ (fun _ : ℕ => (7 : ℤ)) r
                 ↔ ((2 : ℤ) ^ 4 - 3 ^ 2) ∣ (fun _ : ℕ => (7 : ℤ)) 0 :=
  transport_collapse 4 2 (by norm_num) (by norm_num)
    (fun _ => 7) (fun _ => 2) (fun _ => 1) (fun _ => 1) (by intro r; norm_num)

end CollatzTransport

#print axioms CollatzTransport.transport_collapse
#print axioms CollatzTransport.cycle_divisibility_one_check
