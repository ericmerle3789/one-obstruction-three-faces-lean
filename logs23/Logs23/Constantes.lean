import Mathlib
import Logs23.Proposition

/-!
# Logs23 · the constants of step 2b, for every `ν ≥ 335`

Parameters: `L = ν`, `K + 1 = 2^15 ν`, `N = L (K + 1)`, `S = 2^7 ν`, `ζ_max = 2^9 ν`, `λ_max = ν log 2`, `x = 16`.
* `cond_P`: the condition `(P)` of `prop_main` holds for every `b₂ < 2^ν`;
* `final_ge`: `b₂ T' / (N N! (3 X(1))^N L S) ≥ exp(−10^12 ν^5)` whenever `T' ≥ (∏ 1/k!) ((log 2)/2)^(tri N) b₂^(−N²)`.
The proofs take logarithms and use `log ν ≤ ν/50 + 3`, `0.6931 < log 2 < 0.6932`, `n! ≤ n^n`, `σ ≤ N K`,
`tri N = N (N − 1)/2`, then polynomial inequalities in `ν`.
-/

namespace Logs23

open Finset Real

open scoped Nat

noncomputable section

/-! ## Elementary bounds -/

theorem log_le_div50 {v : ℝ} (hv : 0 < v) : Real.log v ≤ v / 50 + 3 := by
  have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < v / 50)
  have h2 : Real.log v = Real.log 50 + Real.log (v / 50) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have h3 : Real.log 50 < 4 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (50 : ℝ) < 2.7182818283 ^ 4 := by norm_num
      _ < Real.exp 1 ^ 4 := by gcongr
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  linarith

theorem log_factorial_le (n : ℕ) : Real.log (n ! : ℝ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have h1 : ((n ! : ℕ) : ℝ) ≤ ((n ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow n
  calc Real.log (n ! : ℝ) ≤ Real.log ((n ^ n : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h1
    _ = n * Real.log n := by push_cast; rw [Real.log_pow]

theorem tri_eq (N : ℕ) : (tri N : ℝ) = N * (N - 1) / 2 := by
  have h : (∑ i ∈ Finset.range N, i) * 2 = N * (N - 1) := Finset.sum_range_id_mul_two N
  have h' : tri N = ∑ i ∈ Finset.range N, i := by
    rw [tri, Fin.sum_univ_eq_sum_range (fun i => i) N]
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp [tri]
  have hc : ((tri N * 2 : ℕ) : ℝ) = ((N * (N - 1) : ℕ) : ℝ) := by rw [h', h]
  push_cast [Nat.cast_sub (show 1 ≤ N from h0)] at hc
  linarith

theorem tri_le (N : ℕ) : (tri N : ℝ) ≤ (N : ℝ) ^ 2 := by
  rw [tri_eq]
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem sig_le (L K : ℕ) : (sig L K : ℝ) ≤ (L * (K + 1) : ℕ) * K := by
  have : sig L K ≤ (L * (K + 1)) * K := by
    calc sig L K = ∑ i : Fin (L * (K + 1)), ((pr i).2 : ℕ) := rfl
      _ ≤ ∑ _i : Fin (L * (K + 1)), K := Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (pr i).2.2
      _ = (L * (K + 1)) * K := by simp
  exact_mod_cast this

/-! ## The parameters -/

/-- `K = 2^15 ν − 1`. -/
def Kp (ν : ℕ) : ℕ := 2 ^ 15 * ν - 1

theorem Kp_succ {ν : ℕ} (hν : 1 ≤ ν) : Kp ν + 1 = 2 ^ 15 * ν := by
  unfold Kp; have : 1 ≤ 2 ^ 15 * ν := by omega
  omega

theorem N_eq {ν : ℕ} (hν : 1 ≤ ν) : ((ν * (Kp ν + 1) : ℕ) : ℝ) = 2 ^ 15 * (ν : ℝ) ^ 2 := by
  rw [Kp_succ hν]; push_cast; ring

theorem K_le {ν : ℕ} : (Kp ν : ℝ) ≤ 2 ^ 15 * ν := by
  have : Kp ν ≤ 2 ^ 15 * ν := Nat.sub_le _ _
  exact_mod_cast this

/-! ## The condition (P) -/

/-- The polynomial inequality behind `(P)`. -/
theorem poly_P {v ℓ t : ℝ} (hv : 335 ≤ v) (hℓ : ℓ ≤ v / 50 + 3) (_hℓ0 : 0 ≤ ℓ) (ht0 : 0.6931 < t)
    (ht1 : t < 0.6932) :
    2 ^ 15 * v ^ 2 * (15 * t + 2 * ℓ) + 2 ^ 15 * v ^ 2 * (2 ^ 15 * v * (13 * t + ℓ) + 2 ^ 13 * v ^ 2 * t)
      - 2 ^ 15 * v ^ 2 * (2 ^ 15 * v ^ 2 - 1) / 2 * (4 * t) + t
      + 2 ^ 15 * v ^ 2 * (2 ^ 15 * v) * (v * t) ≤ 0 := by
  have hv0 : 0 < v := by linarith
  have h3 : v ^ 3 * 335 ≤ v ^ 4 := by nlinarith [pow_pos hv0 3]
  nlinarith [pow_pos hv0 2, pow_pos hv0 3, pow_pos hv0 4, mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 3).le,
    mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 2).le]

theorem cond_P {ν : ℕ} (hν : 335 ≤ ν) {b₂ : ℕ} (hb : 0 < b₂) (hb₂ : (b₂ : ℝ) < 2 ^ ν) :
    (((ν * (Kp ν + 1)) ! : ℕ) : ℝ) * Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 16 ^ (ν * (Kp ν + 1)) /
        16 ^ tri (ν * (Kp ν + 1)) ≤ 1 / (2 * (b₂ : ℝ) ^ sig ν (Kp ν)) := by
  set N := ν * (Kp ν + 1) with hN
  have hν1 : 1 ≤ ν := by omega
  have hv : (335 : ℝ) ≤ ν := by exact_mod_cast hν
  have hv0 : (0 : ℝ) < ν := by linarith
  have hNr : (N : ℝ) = 2 ^ 15 * (ν : ℝ) ^ 2 := N_eq hν1
  have hN0 : (0 : ℝ) < N := by rw [hNr]; positivity
  have ht0 := Real.log_two_gt_d9
  have ht1 := Real.log_two_lt_d9
  have hb0 : (0 : ℝ) < b₂ := by exact_mod_cast hb
  -- both sides are positive; compare logarithms
  have hX : 0 < Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 16 := by unfold Xb; positivity
  have hL : 0 < ((N ! : ℕ) : ℝ) * Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 16 ^ N / 16 ^ tri N := by
    have := Nat.factorial_pos N; positivity
  have hR : 0 < 1 / (2 * (b₂ : ℝ) ^ sig ν (Kp ν)) := by positivity
  rw [← Real.log_le_log_iff hL hR]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by have := Nat.factorial_pos N; positivity)
    (by positivity), Real.log_pow, Real.log_pow, Real.log_div one_ne_zero (by positivity), Real.log_one,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hXlog : Real.log (Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 16) =
      Kp ν * (13 * Real.log 2 + Real.log ν) + 2 ^ 13 * (ν : ℝ) ^ 2 * Real.log 2 := by
    unfold Xb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp,
      show (16 : ℝ) * (2 ^ 9 * ν) = 2 ^ 13 * ν by ring, Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast; ring
  rw [hXlog]
  have hfact := log_factorial_le N
  have hlogN : Real.log N = 15 * Real.log 2 + 2 * Real.log ν := by
    rw [hNr, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  have hlogb : Real.log b₂ ≤ ν * Real.log 2 := by
    have := Real.log_lt_log hb0 hb₂
    rw [Real.log_pow] at this; linarith
  have hlogb0 : 0 ≤ Real.log b₂ := Real.log_nonneg (by exact_mod_cast hb)
  have hsig := sig_le ν (Kp ν)
  have hK := K_le (ν := ν)
  have hK0 : (0 : ℝ) ≤ Kp ν := Nat.cast_nonneg _
  have hℓ := log_le_div50 hv0
  have hℓ0 : 0 ≤ Real.log ν := Real.log_nonneg (by linarith)
  have htri := tri_eq N
  rw [hlog16, htri]
  have hP := poly_P hv hℓ hℓ0 (by linarith : (0.6931 : ℝ) < Real.log 2) (by linarith : Real.log 2 < 0.6932)
  rw [hlogN] at hfact
  rw [hNr] at hfact hsig htri ⊢
  -- assemble
  have e1 : (sig ν (Kp ν) : ℝ) * Real.log b₂ ≤ 2 ^ 15 * (ν : ℝ) ^ 2 * (2 ^ 15 * ν) * (ν * Real.log 2) := by
    have hs0 : (0 : ℝ) ≤ sig ν (Kp ν) := Nat.cast_nonneg _
    calc (sig ν (Kp ν) : ℝ) * Real.log b₂ ≤ (2 ^ 15 * (ν : ℝ) ^ 2 * Kp ν) * (ν * Real.log 2) :=
          mul_le_mul hsig hlogb hlogb0 (by positivity)
      _ ≤ 2 ^ 15 * (ν : ℝ) ^ 2 * (2 ^ 15 * ν) * (ν * Real.log 2) := by gcongr
  have e2 : 2 ^ 15 * (ν : ℝ) ^ 2 * (Kp ν * (13 * Real.log 2 + Real.log ν) + 2 ^ 13 * (ν : ℝ) ^ 2 * Real.log 2) ≤
      2 ^ 15 * (ν : ℝ) ^ 2 * (2 ^ 15 * ν * (13 * Real.log 2 + Real.log ν) + 2 ^ 13 * (ν : ℝ) ^ 2 * Real.log 2) := by
    have : (0 : ℝ) ≤ 13 * Real.log 2 + Real.log ν := by linarith
    gcongr
  nlinarith

/-! ## The final bound -/

/-- The polynomial inequality behind the final bound (`N = 2^15 v²`, `log N = 15 t + 2 ℓ`, `t = log 2`,
`u = log 3`, `ℓ = log ν`). -/
theorem poly_final {v ℓ t : ℝ} (hv : 335 ≤ v) (hℓ : ℓ ≤ v / 50 + 3) (_hℓ0 : 0 ≤ ℓ) (ht0 : 0.6931 < t)
    (ht1 : t < 0.6932) (u : ℝ) (_hu0 : 0 ≤ u) (hu : u ≤ 2) :
    (15 * t + 2 * ℓ) + 2 ^ 15 * v ^ 2 * (15 * t + 2 * ℓ)
      + 2 ^ 15 * v ^ 2 * (u + (2 ^ 15 * v * (9 * t + ℓ) + v * t * (2 ^ 9 * v))) + (7 * t + 2 * ℓ)
      + 2 ^ 15 * v ^ 2 * (2 ^ 15 * v ^ 2 * (15 * t + 2 * ℓ)) + (2 ^ 15 * v ^ 2) ^ 2 * u
      + (2 ^ 15 * v ^ 2) ^ 2 * (v * t) ≤ 10 ^ 12 * v ^ 5 := by
  have hv0 : 0 < v := by linarith
  nlinarith [pow_pos hv0 2, pow_pos hv0 3, pow_pos hv0 4, pow_pos hv0 5,
    mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 4).le, mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 2).le,
    mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 3).le]

theorem log_three_le : Real.log 3 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := Real.exp_one_gt_d9
  calc (3 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
    _ ≤ Real.exp 1 ^ 2 := by gcongr
    _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num

/-- **The final bound.** -/
theorem final_ge {ν : ℕ} (hν : 335 ≤ ν) {b₂ : ℕ} (hb : 0 < b₂) (hb₂ : (b₂ : ℝ) < 2 ^ ν) {T : ℝ}
    (hT : (∏ k : Fin (ν * (Kp ν + 1)), (1 / ((k : ℕ)! : ℝ))) * (Real.log 2 / 2) ^ tri (ν * (Kp ν + 1)) *
      (1 / (b₂ : ℝ)) ^ ((ν * (Kp ν + 1)) ^ 2) ≤ T) :
    Real.exp (-(10 ^ 12 * (ν : ℝ) ^ 5)) ≤
      (b₂ : ℝ) * T / (((ν * (Kp ν + 1) : ℕ) : ℝ) * (((ν * (Kp ν + 1)) ! : ℕ) : ℝ) *
        (3 * Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 1) ^ (ν * (Kp ν + 1)) * ((ν : ℝ) * (2 ^ 7 * ν : ℕ))) := by
  set N := ν * (Kp ν + 1) with hN
  have hν1 : 1 ≤ ν := by omega
  have hv : (335 : ℝ) ≤ ν := by exact_mod_cast hν
  have hv0 : (0 : ℝ) < ν := by linarith
  have hNr : (N : ℝ) = 2 ^ 15 * (ν : ℝ) ^ 2 := N_eq hν1
  have hN0 : (0 : ℝ) < N := by rw [hNr]; positivity
  have ht0 := Real.log_two_gt_d9
  have ht1 := Real.log_two_lt_d9
  have hlog2 : 0 < Real.log 2 := by linarith
  have hb0 : (0 : ℝ) < b₂ := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b₂ := by exact_mod_cast hb
  set X1 := Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 1 with hX1
  have hX1p : 0 < X1 := by unfold Xb at hX1; rw [hX1]; positivity
  set c := Real.log 2 / 2 with hc
  have hc0 : 0 < c := by positivity
  set T0 := (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * c ^ tri N * (1 / (b₂ : ℝ)) ^ (N ^ 2) with hT0
  have hT0p : 0 < T0 := by
    have : 0 < ∏ k : Fin N, (1 / ((k : ℕ)! : ℝ)) := Finset.prod_pos fun k _ => by positivity
    positivity
  set den := (N : ℝ) * ((N ! : ℕ) : ℝ) * (3 * X1) ^ N * ((ν : ℝ) * (2 ^ 7 * ν : ℕ)) with hden
  have hdenp : 0 < den := by have := Nat.factorial_pos N; positivity
  -- `log den − log T0 ≤ 10^12 ν^5`
  have hℓ := log_le_div50 hv0
  have hℓ0 : 0 ≤ Real.log ν := Real.log_nonneg (by linarith)
  have hlogN : Real.log N = 15 * Real.log 2 + 2 * Real.log ν := by
    rw [hNr, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  have hfactN := log_factorial_le N
  have hlogT0 : -((N : ℝ) * ((N : ℝ) * Real.log N)) - (N : ℝ) ^ 2 * Real.log 3 - (N : ℝ) ^ 2 * (ν * Real.log 2) ≤
      Real.log T0 := by
    rw [hT0, Real.log_mul (by positivity) (by positivity), Real.log_mul (by
      exact (Finset.prod_pos fun k _ => by positivity).ne') (by positivity),
      Real.log_prod (fun k _ => by positivity), Real.log_pow, Real.log_pow, one_div, Real.log_inv]
    have h1 : -((N : ℝ) * ((N : ℝ) * Real.log N)) ≤ ∑ k : Fin N, Real.log (1 / ((k : ℕ)! : ℝ)) := by
      have : ∀ k : Fin N, -((N : ℝ) * Real.log N) ≤ Real.log (1 / ((k : ℕ)! : ℝ)) := by
        intro k
        rw [one_div, Real.log_inv, neg_le_neg_iff]
        have hk : ((k : ℕ)! : ℝ) ≤ (N ! : ℝ) := by exact_mod_cast Nat.factorial_le k.2.le
        exact (Real.log_le_log (by positivity) hk).trans hfactN
      calc -((N : ℝ) * ((N : ℝ) * Real.log N)) = ∑ _k : Fin N, -((N : ℝ) * Real.log N) := by simp
        _ ≤ _ := Finset.sum_le_sum fun k _ => this k
    have h2 : -((N : ℝ) ^ 2 * Real.log 3) ≤ (tri N : ℝ) * Real.log c := by
      have hc3 : (1 : ℝ) / 3 ≤ c := by rw [hc]; linarith
      have hlc : -Real.log 3 ≤ Real.log c := by
        have := Real.log_le_log (by norm_num) hc3
        rwa [one_div, Real.log_inv] at this
      have hlc0 : Real.log c ≤ 0 := Real.log_nonpos hc0.le (by rw [hc]; linarith)
      have htri := tri_le N
      have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have ht0' : (0 : ℝ) ≤ tri N := Nat.cast_nonneg _
      nlinarith
    have h3 : -((N : ℝ) ^ 2 * (ν * Real.log 2)) ≤ ((N ^ 2 : ℕ) : ℝ) * -Real.log b₂ := by
      have := Real.log_lt_log hb0 hb₂
      rw [Real.log_pow] at this
      push_cast
      have : 0 ≤ (N : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  have hlogden : Real.log den ≤ Real.log N + (N : ℝ) * Real.log N + (N : ℝ) * (Real.log 3 +
      (2 ^ 15 * ν * (9 * Real.log 2 + Real.log ν) + ν * Real.log 2 * (2 ^ 9 * ν))) + (7 * Real.log 2 + 2 * Real.log ν) := by
    rw [hden, Real.log_mul (by positivity) (by positivity), Real.log_mul (by have := Nat.factorial_pos N; positivity)
      (by positivity), Real.log_mul (by positivity) (by have := Nat.factorial_pos N; positivity), Real.log_pow,
      Real.log_mul (by norm_num) hX1p.ne']
    have hXl : Real.log X1 ≤ 2 ^ 15 * ν * (9 * Real.log 2 + Real.log ν) + ν * Real.log 2 * (2 ^ 9 * ν) := by
      rw [hX1, Xb, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp,
        show (1 : ℝ) * (2 ^ 9 * ν) = 2 ^ 9 * ν by ring, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hK := K_le (ν := ν)
      have : (0 : ℝ) ≤ 9 * Real.log 2 + Real.log ν := by linarith
      push_cast
      have h' : (Kp ν : ℝ) * (9 * Real.log 2 + Real.log ν) ≤ 2 ^ 15 * ν * (9 * Real.log 2 + Real.log ν) := by gcongr
      linarith
    have hLS : Real.log ((ν : ℝ) * (2 ^ 7 * ν : ℕ)) = 7 * Real.log 2 + 2 * Real.log ν := by
      push_cast
      rw [show (ν : ℝ) * (128 * ν) = 2 ^ 7 * (ν : ℝ) ^ 2 by ring, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]; push_cast; ring
    rw [hLS]
    have hNX := mul_le_mul_of_nonneg_left hXl hN0.le
    linarith
  have hpoly := poly_final hv hℓ hℓ0 (by linarith : (0.6931 : ℝ) < Real.log 2)
    (by linarith : Real.log 2 < 0.6932) (Real.log 3) (Real.log_nonneg (by norm_num)) log_three_le
  have hkey : Real.log den - Real.log T0 ≤ 10 ^ 12 * (ν : ℝ) ^ 5 := by
    rw [hlogN] at hlogT0 hlogden
    rw [hNr] at hlogT0 hlogden
    linarith
  -- conclude
  have hq : Real.exp (-(10 ^ 12 * (ν : ℝ) ^ 5)) ≤ T0 / den := by
    rw [← Real.exp_log (by positivity : 0 < T0 / den), Real.log_div hT0p.ne' hdenp.ne']
    exact Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (-(10 ^ 12 * (ν : ℝ) ^ 5)) ≤ T0 / den := hq
    _ ≤ T / den := by gcongr
    _ ≤ (b₂ : ℝ) * T / den := by
        have hT : 0 ≤ T := le_trans hT0p.le hT
        rw [mul_div_assoc]
        exact le_mul_of_one_le_left (by positivity) hb1

end

end Logs23
