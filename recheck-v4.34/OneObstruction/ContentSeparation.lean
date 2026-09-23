/-
ContentSeparation.lean — The content separation lemma (T1/T2), kernel-checked.
Session 2026-07-24, A.R.E.S. protocol (Merle side).

SCOPE, stated honestly.
A word is a list of letters (m, s) ∈ ℕ². The object formalized is the 2-shifted
rotation numerator, defined by the fold

  W0 []              = 0
  W0 ((m,s) :: rest) = 3^(msum rest) · 2^m · (2^s − 1) + 2^(m+s) · W0 rest.

Bridge to the Python-side R₀ (REQ-MATH-003..019): W0(l) = 2^(m₀) · R₀(l) for
nonempty l — verified numerically, exact big-int, in
experiments/test_REQ-MATH-020_pont_lean.py. Since the seam modulus
q = 2^K − 3^n is ODD (and prime to 3), gcd(q, W0) = gcd(q, R₀): every divisor
statement below transfers verbatim to R₀.

REDUCED vs UNREDUCED MODULUS (explicit, per review). Every statement below is about
the UNREDUCED seam modulus q = 2^K − 3^n — never the reduced denominator q / gcd(q, R₀).
The two differ exactly when gcd(q, R₀) > 1 (concretely the p = 7 seed, where gcd = 7:
q carries a factor 7 that R₀ does not fully carry). The separation theorems quantify over
an ARBITRARY divisor d ∣ q, hence cover every prime power of the unreduced q; and
`q_divisor_coprime` is stated for d ∣ (2^K − 3^n) with no reduction assumed. In W0 coordinates the m-transfer at
position 0 is REGULAR (no wrap-around pathology): T2 below holds at every
position, strengthening the rotation-reduction used on the Python side.

Theorems (all 0 sorry, no user axioms, no native_decide):
  T1  s-transfer difference:  W0(P') − W0(P) = 2^(mssum pre) · 3^(msum suf) · 2^(m₁+s₁) · (3^m₂ − 2^m₂)
  T2  m-transfer difference:  W0(P') − W0(P) = −(2^(mssum pre) · 3^(m₂+msum suf) · 2^m₁ · (2^s₁ − 1))
  separation_T1 / separation_T2 : a common divisor of the two neighbours that is
    coprime to 2 and 3 divides the LETTER-SCALE seam (3^m₂ − 2^m₂, resp. 2^s₁ − 1).
  q_divisor_coprime : every divisor of q = 2^K − 3^n (K, n ≥ 1) is coprime to 2 and 3
    — so the separation applies to every divisor of the seam modulus.
Non-vacuity canaries at the end (norm_num, no native_decide).
-/
import Mathlib

namespace ContentSeparation

/-- Sum of the m-components of a word. -/
def msum (l : List (ℕ × ℕ)) : ℕ := (l.map Prod.fst).sum

/-- Sum of m+s over the word (the 2-exponent weight of a prefix). -/
def mssum (l : List (ℕ × ℕ)) : ℕ := (l.map fun x => x.1 + x.2).sum

/-- The 2-shifted rotation numerator, as a fold (W0 = 2^(m₀)·R₀; see header). -/
def W0 : List (ℕ × ℕ) → ℤ
  | [] => 0
  | (m, s) :: rest => 3 ^ msum rest * 2 ^ m * (2 ^ s - 1) + 2 ^ (m + s) * W0 rest

@[simp] lemma msum_nil : msum [] = 0 := rfl
@[simp] lemma msum_cons (m s : ℕ) (l : List (ℕ × ℕ)) :
    msum ((m, s) :: l) = m + msum l := by simp [msum]
lemma msum_append (l₁ l₂ : List (ℕ × ℕ)) :
    msum (l₁ ++ l₂) = msum l₁ + msum l₂ := by simp [msum]
@[simp] lemma mssum_nil : mssum [] = 0 := rfl
@[simp] lemma mssum_cons (m s : ℕ) (l : List (ℕ × ℕ)) :
    mssum ((m, s) :: l) = (m + s) + mssum l := by simp [mssum]
@[simp] lemma W0_nil : W0 [] = 0 := rfl
lemma W0_cons (m s : ℕ) (rest : List (ℕ × ℕ)) :
    W0 ((m, s) :: rest)
      = 3 ^ msum rest * 2 ^ m * (2 ^ s - 1) + 2 ^ (m + s) * W0 rest := rfl

/-- A shared prefix scales the difference by 2^(mssum pre), provided the two
    tails carry the same total m-mass (the 3-exponents seen by the prefix agree). -/
lemma W0_prefix_diff (pre : List (ℕ × ℕ)) {r₁ r₂ : List (ℕ × ℕ)}
    (h : msum r₁ = msum r₂) :
    W0 (pre ++ r₁) - W0 (pre ++ r₂) = 2 ^ mssum pre * (W0 r₁ - W0 r₂) := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      obtain ⟨m, s⟩ := a
      calc W0 (((m, s) :: pre) ++ r₁) - W0 (((m, s) :: pre) ++ r₂)
          = 2 ^ (m + s) * (W0 (pre ++ r₁) - W0 (pre ++ r₂)) := by
            simp only [List.cons_append, W0_cons, msum_append, h]
            ring
        _ = 2 ^ (m + s) * (2 ^ mssum pre * (W0 r₁ - W0 r₂)) := by rw [ih]
        _ = 2 ^ mssum ((m, s) :: pre) * (W0 r₁ - W0 r₂) := by
            rw [mssum_cons, pow_add]; ring

/-- **T1 (s-transfer).** Moving one unit of s across an adjacent pair
    (same seam modulus q) changes W0 by a letter-scale seam factor. -/
theorem T1 (pre suf : List (ℕ × ℕ)) (m₁ s₁ m₂ c : ℕ) :
    W0 (pre ++ (m₁, s₁ + 1) :: (m₂, c) :: suf)
      - W0 (pre ++ (m₁, s₁) :: (m₂, c + 1) :: suf)
      = 2 ^ mssum pre * (3 ^ msum suf * 2 ^ (m₁ + s₁) * (3 ^ m₂ - 2 ^ m₂)) := by
  rw [W0_prefix_diff pre (by simp)]
  simp only [W0_cons, msum_cons, pow_add, pow_succ]
  ring

/-- **T2 (m-transfer).** Moving one unit of m across an adjacent pair changes W0
    by minus a letter-scale factor. In W0 coordinates this holds at EVERY position
    — the position-0 boundary case is regular here. -/
theorem T2 (pre suf : List (ℕ × ℕ)) (m₁ s₁ m₂ s₂ : ℕ) :
    W0 (pre ++ (m₁ + 1, s₁) :: (m₂, s₂) :: suf)
      - W0 (pre ++ (m₁, s₁) :: (m₂ + 1, s₂) :: suf)
      = -(2 ^ mssum pre * (3 ^ (m₂ + msum suf) * 2 ^ m₁ * (2 ^ s₁ - 1))) := by
  rw [W0_prefix_diff pre (by simp; omega)]
  simp only [W0_cons, msum_cons, pow_add, pow_succ]
  ring

/-- **Separation (s-transfer).** A divisor coprime to 2 and 3 shared by the two
    neighbours divides the letter-scale seam 3^m₂ − 2^m₂. -/
theorem separation_T1 (d : ℤ) (h2 : IsCoprime d 2) (h3 : IsCoprime d 3)
    (pre suf : List (ℕ × ℕ)) (m₁ s₁ m₂ c : ℕ)
    (hP : d ∣ W0 (pre ++ (m₁, s₁ + 1) :: (m₂, c) :: suf))
    (hP' : d ∣ W0 (pre ++ (m₁, s₁) :: (m₂, c + 1) :: suf)) :
    d ∣ 3 ^ m₂ - 2 ^ m₂ := by
  have h := dvd_sub hP hP'
  rw [T1 pre suf m₁ s₁ m₂ c] at h
  have s1 : d ∣ 3 ^ msum suf * 2 ^ (m₁ + s₁) * (3 ^ m₂ - 2 ^ m₂) :=
    (h2.pow_right).dvd_of_dvd_mul_left h
  exact ((h3.pow_right).mul_right (h2.pow_right)).dvd_of_dvd_mul_left s1

/-- **Separation (m-transfer).** A divisor coprime to 2 and 3 shared by the two
    neighbours divides the letter-scale seam 2^s₁ − 1. Valid at every position. -/
theorem separation_T2 (d : ℤ) (h2 : IsCoprime d 2) (h3 : IsCoprime d 3)
    (pre suf : List (ℕ × ℕ)) (m₁ s₁ m₂ s₂ : ℕ)
    (hP : d ∣ W0 (pre ++ (m₁ + 1, s₁) :: (m₂, s₂) :: suf))
    (hP' : d ∣ W0 (pre ++ (m₁, s₁) :: (m₂ + 1, s₂) :: suf)) :
    d ∣ 2 ^ s₁ - 1 := by
  have h := dvd_sub hP hP'
  rw [T2 pre suf m₁ s₁ m₂ s₂] at h
  have h' : d ∣ 2 ^ mssum pre * (3 ^ (m₂ + msum suf) * 2 ^ m₁ * (2 ^ s₁ - 1)) :=
    (dvd_neg).mp h
  have s1 : d ∣ 3 ^ (m₂ + msum suf) * 2 ^ m₁ * (2 ^ s₁ - 1) :=
    (h2.pow_right).dvd_of_dvd_mul_left h'
  exact ((h3.pow_right).mul_right (h2.pow_right)).dvd_of_dvd_mul_left s1

/-- 2 does not divide the seam modulus q = 2^K − 3^n (K ≥ 1). -/
lemma two_not_dvd_q {K n : ℕ} (hK : 1 ≤ K) : ¬ (2 : ℤ) ∣ (2 ^ K - 3 ^ n) := by
  intro h
  have h2K : (2 : ℤ) ∣ 2 ^ K := dvd_pow_self 2 (by omega)
  have h3n : (2 : ℤ) ∣ 3 ^ n := by
    have h' := dvd_sub h2K h
    rwa [sub_sub_cancel] at h'
  have := Int.prime_two.dvd_of_dvd_pow h3n
  norm_num at this

/-- 3 does not divide the seam modulus q = 2^K − 3^n (n ≥ 1). -/
lemma three_not_dvd_q {K n : ℕ} (hn : 1 ≤ n) : ¬ (3 : ℤ) ∣ (2 ^ K - 3 ^ n) := by
  intro h
  have h3n : (3 : ℤ) ∣ 3 ^ n := dvd_pow_self 3 (by omega)
  have h2K : (3 : ℤ) ∣ 2 ^ K := by
    have h' := dvd_add h h3n
    rwa [sub_add_cancel] at h'
  have := Int.prime_three.dvd_of_dvd_pow h2K
  norm_num at this

/-- Every divisor of the seam modulus q = 2^K − 3^n (K, n ≥ 1) is coprime to 2
    and to 3 — so the separation theorems apply to every divisor of q. -/
lemma q_divisor_coprime {d : ℤ} {K n : ℕ} (hK : 1 ≤ K) (hn : 1 ≤ n)
    (hd : d ∣ 2 ^ K - 3 ^ n) : IsCoprime d 2 ∧ IsCoprime d 3 := by
  constructor
  · have : ¬ (2 : ℤ) ∣ d := fun h => two_not_dvd_q (n := n) hK (h.trans hd)
    exact ((Int.prime_two.coprime_iff_not_dvd).mpr this).symm
  · have : ¬ (3 : ℤ) ∣ d := fun h => three_not_dvd_q (K := K) hn (h.trans hd)
    exact ((Int.prime_three.coprime_iff_not_dvd).mpr this).symm

/- ===== Non-vacuity canaries (norm_num only; no native_decide) ===== -/

/-- Canary 1: trivial word squared — W0 [(1,1),(1,1)] = 14 = 2^(m₀)·R₀ with R₀ = 7. -/
example : W0 [(1, 1), (1, 1)] = 14 := by
  norm_num [W0, msum]

/-- Canary 2: a full numeric instance of T1 (pre = suf = [], letters (2,3),(3,2)):
    the difference is exactly 2^5·(3^3 − 2^3) = 608. -/
example : W0 [(2, 4), (3, 1)] - W0 [(2, 3), (3, 2)] = 608 := by
  norm_num [W0, msum]

/-- Canary 3: a full numeric instance of T2 at position 0 (regular in W0 form):
    W0 [(2,1),(1,3)] − W0 [(1,1),(2,3)] = −(3^1·2^1·(2^1−1)) = −6. -/
example : W0 [(2, 1), (1, 3)] - W0 [(1, 1), (2, 3)] = -6 := by
  norm_num [W0, msum]

#print axioms T1
#print axioms T2
#print axioms separation_T1
#print axioms separation_T2
#print axioms q_divisor_coprime

end ContentSeparation
