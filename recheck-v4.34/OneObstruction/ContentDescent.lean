/-
ContentDescent.lean — The structured half, kernel-checked (L-A4 + the climb law).
Session 2026-07-24, A.R.E.S. protocol (Merle side).

SCOPE. Same object as ContentSeparation.lean: the 2-shifted numerator W0 (fold form;
W0 = 2^(m₀)·R₀, bridge canary REQ-MATH-020; q odd ⇒ same gcd with q). UNREDUCED modulus
throughout: q(l) = 2^(mssum l) − 3^(msum l), never q/gcd. Statements:

  W0_append    cocycle:  W0(l₁ ++ l₂) = 3^(msum l₂)·W0 l₁ + 2^(mssum l₁)·W0 l₂
  power_mult   Macindoe's multiplicative identity (W0 form): W0(B^k) = G_k · W0(B)
  q_pow_factor the seam modulus scales by the SAME cofactor: q(B^k) = G_k · q(B)
  cycle_iff    descent/inheritance, both directions (k ≥ 1): q(B^k) ∣ W0(B^k) ↔ q(B) ∣ W0(B)
  gcd_climb    the climb law (L-A2 general form): gcd(q(B^k), W0(B^k)) = |G_k| · gcd(q(B), W0(B))

with G_k = geom l k = Σ_{i<k} 2^(i·K)·3^((k−1−i)·n) (recursive definition), G_k > 0 for k ≥ 1.
All 0 sorry, no user axioms, no native_decide. Non-vacuity canaries at the end.
-/
import Mathlib

namespace ContentDescent

def msum (l : List (ℕ × ℕ)) : ℕ := (l.map Prod.fst).sum
def mssum (l : List (ℕ × ℕ)) : ℕ := (l.map fun x => x.1 + x.2).sum

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
lemma mssum_append (l₁ l₂ : List (ℕ × ℕ)) :
    mssum (l₁ ++ l₂) = mssum l₁ + mssum l₂ := by simp [mssum]
@[simp] lemma W0_nil : W0 [] = 0 := rfl
lemma W0_cons (m s : ℕ) (rest : List (ℕ × ℕ)) :
    W0 ((m, s) :: rest)
      = 3 ^ msum rest * 2 ^ m * (2 ^ s - 1) + 2 ^ (m + s) * W0 rest := rfl

/-- **Cocycle.** W0 over a concatenation: the left block sees the right block only
    through its 3-mass; the right block is shifted by the left block's full 2-weight. -/
lemma W0_append (l₁ l₂ : List (ℕ × ℕ)) :
    W0 (l₁ ++ l₂) = 3 ^ msum l₂ * W0 l₁ + 2 ^ mssum l₁ * W0 l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
      obtain ⟨m, s⟩ := a
      simp only [List.cons_append, W0_cons, msum_append, mssum_cons, ih, pow_add]
      ring

/-- k-fold repetition of a word. -/
def rep (l : List (ℕ × ℕ)) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | k + 1 => l ++ rep l k

@[simp] lemma rep_zero (l : List (ℕ × ℕ)) : rep l 0 = [] := rfl
lemma rep_succ (l : List (ℕ × ℕ)) (k : ℕ) : rep l (k + 1) = l ++ rep l k := rfl

lemma msum_rep (l : List (ℕ × ℕ)) (k : ℕ) : msum (rep l k) = k * msum l := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, msum_append, ih]; ring

lemma mssum_rep (l : List (ℕ × ℕ)) (k : ℕ) : mssum (rep l k) = k * mssum l := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, mssum_append, ih]; ring

/-- The geometric cofactor G_k (recursive form). -/
def geom (l : List (ℕ × ℕ)) : ℕ → ℤ
  | 0 => 0
  | k + 1 => 3 ^ (k * msum l) + 2 ^ mssum l * geom l k

/-- **Macindoe's multiplicative identity, W0 form:** W0(B^k) = G_k · W0(B). -/
theorem power_mult (l : List (ℕ × ℕ)) (k : ℕ) :
    W0 (rep l k) = geom l k * W0 l := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
      rw [rep_succ, W0_append, msum_rep, ih]
      simp only [geom]
      ring

/-- **The seam modulus scales by the same cofactor:** q(B^k) = G_k · q(B). -/
theorem q_pow_factor (l : List (ℕ × ℕ)) (k : ℕ) :
    (2 : ℤ) ^ (k * mssum l) - 3 ^ (k * msum l)
      = geom l k * ((2 : ℤ) ^ mssum l - 3 ^ msum l) := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
      have h2 : (k + 1) * mssum l = mssum l + k * mssum l := by ring
      have h3 : (k + 1) * msum l = msum l + k * msum l := by ring
      simp only [geom, h2, h3, pow_add]
      linear_combination (2 : ℤ) ^ mssum l * ih

lemma geom_nonneg (l : List (ℕ × ℕ)) (k : ℕ) : 0 ≤ geom l k := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
      simp only [geom]
      exact add_nonneg (by positivity) (mul_nonneg (by positivity) ih)

lemma geom_pos (l : List (ℕ × ℕ)) (k : ℕ) : 0 < geom l (k + 1) := by
  simp only [geom]
  exact add_pos_of_pos_of_nonneg (by positivity)
    (mul_nonneg (by positivity) (geom_nonneg l k))

/-- **Descent / inheritance, both directions (k ≥ 1):** a repeated word is a cycle
    exactly when its base is — no new cycle is ever created by repetition (L-A4). -/
theorem cycle_iff (l : List (ℕ × ℕ)) (k : ℕ) (hk : 1 ≤ k) :
    ((2 : ℤ) ^ (k * mssum l) - 3 ^ (k * msum l)) ∣ W0 (rep l k)
      ↔ ((2 : ℤ) ^ mssum l - 3 ^ msum l) ∣ W0 l := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [power_mult, q_pow_factor]
  exact mul_dvd_mul_iff_left (geom_pos l k).ne'

/-- **The climb law (L-A2 general form):** the content cofactor of a power is exactly G_k. -/
theorem gcd_climb (l : List (ℕ × ℕ)) (k : ℕ) :
    Int.gcd ((2 : ℤ) ^ (k * mssum l) - 3 ^ (k * msum l)) (W0 (rep l k))
      = (geom l k).natAbs * Int.gcd ((2 : ℤ) ^ mssum l - 3 ^ msum l) (W0 l) := by
  rw [power_mult, q_pow_factor]
  exact Int.gcd_mul_left _ _ _

/- ===== Non-vacuity canaries (norm_num only) ===== -/

/-- Canary 1: trivial word, k = 2 — W0 doubles by the cofactor 7 (= q of the square). -/
example : W0 [(1, 1), (1, 1)] = 7 * W0 [(1, 1)] := by
  norm_num [W0, msum]

/-- Canary 2: the trivial square is a cycle: q = 2^4 − 3^2 = 7 divides W0 = 14. -/
example : ((2 : ℤ) ^ 4 - 3 ^ 2) ∣ W0 [(1, 1), (1, 1)] := by
  norm_num [W0, msum]

#print axioms W0_append
#print axioms power_mult
#print axioms q_pow_factor
#print axioms cycle_iff
#print axioms gcd_climb

end ContentDescent
