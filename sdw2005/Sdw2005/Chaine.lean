import Mathlib
import Sdw2005.Sdw_Enonces

/-!
# Sdw2005 · Lemmas 4, 6 and 7 of Simons–de Weger (chain equation, `X0 = 1`)
-/

namespace Sdw2005

open Finset

/-! ## Rotations of indices modulo `m` -/

theorem sum_rot_one (m : ℕ) (hm : 0 < m) (g : ℕ → ℝ) :
    ∑ i ∈ range m, g ((i + 1) % m) = ∑ i ∈ range m, g i := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have h1 : ∀ i ∈ range n, g ((i + 1) % (n + 1)) = g (i + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [Finset.sum_congr rfl h1, Nat.mod_self]

theorem sum_rot (m : ℕ) (hm : 0 < m) (f : ℕ → ℝ) (s : ℕ) :
    ∑ i ∈ range m, f ((s + i) % m) = ∑ i ∈ range m, f i := by
  induction s with
  | zero =>
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.zero_add, Nat.mod_eq_of_lt hi]
  | succ s ih =>
    have h1 : ∀ i ∈ range m, f ((s + 1 + i) % m) = (fun j => f ((s + j) % m)) ((i + 1) % m) := by
      intro i _
      simp only
      rw [Nat.add_mod_mod, show s + (i + 1) = s + 1 + i by omega]
    rw [Finset.sum_congr rfl h1, sum_rot_one m hm (fun j => f ((s + j) % m)), ih]

/-! ## Elementary facts on a solution -/

theorem one_le_xm {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSol m k l a) {i : ℕ} (hi : i < m) :
    1 ≤ xm k a i := by
  obtain ⟨hk, -, ha, -⟩ := h.2 i hi
  have h2 : 2 ≤ 2 ^ k i := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k i := Nat.pow_le_pow_right (by norm_num) hk
  have : 2 ≤ 2 ^ k i * a i := le_trans h2 (Nat.le_mul_of_pos_right _ ha)
  unfold xm
  omega

theorem xm_cast {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSol m k l a) {i : ℕ} (hi : i < m) :
    (xm k a i : ℝ) = (2 : ℝ) ^ k i * a i - 1 := by
  have h1 := one_le_xm h hi
  have h2 : 1 ≤ 2 ^ k i * a i := by unfold xm at h1; omega
  rw [xm, Nat.cast_sub h2]
  push_cast
  ring

theorem xm_pos {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSol m k l a) {i : ℕ} (hi : i < m) :
    (1 : ℝ) ≤ (xm k a i : ℝ) := by
  exact_mod_cast one_le_xm h hi

/-- The chain equation in the reals: `3^{k_i} a_i = 2^{l_i} x_{i+1} + 1`. -/
theorem chain_real {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSol m k l a) {i : ℕ} (hi : i < m) :
    (3 : ℝ) ^ k i * a i = 2 ^ l i * (xm k a ((i + 1) % m) : ℝ) + 1 := by
  have hj : (i + 1) % m < m := Nat.mod_lt _ h.1
  obtain ⟨-, -, -, he⟩ := h.2 i hi
  have hr : ((3 : ℝ) ^ k i * a i - 1) = 2 ^ (k ((i + 1) % m) + l i) * a ((i + 1) % m) - 2 ^ l i := by
    exact_mod_cast he
  rw [xm_cast h hj]
  rw [pow_add] at hr
  linear_combination hr

/-! ## Lemma 4 -/

theorem lemma4_thm : lemma4 := by
  intro m k l a h
  have hm : 0 < m := h.1
  have hj : ∀ i, (i + 1) % m < m := fun i => Nat.mod_lt _ hm
  -- the factors `1 + ε_i`
  set ε : ℕ → ℝ := fun i => ((2 : ℝ) ^ l i - 1) / ((3 : ℝ) ^ k i * a i) with hε
  have hA : ∀ i < m, 0 < (3 : ℝ) ^ k i * a i := by
    intro i hi
    have ha : (0 : ℝ) < a i := by exact_mod_cast (h.2 i hi).2.2.1
    positivity
  have hl2 : ∀ i < m, (2 : ℝ) ≤ 2 ^ l i := by
    intro i hi
    have := (h.2 i hi).2.1
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l i := pow_le_pow_right₀ (by norm_num) this
  have hεpos : ∀ i < m, 0 < ε i := by
    intro i hi
    have := hl2 i hi
    exact div_pos (by linarith) (hA i hi)
  -- `log (1 + ε_i)` as a difference of logarithms
  have hkey : ∀ i ∈ range m, Real.log (1 + ε i) =
      ((k ((i + 1) % m) : ℝ) * Real.log 2 + Real.log (a ((i + 1) % m))) + (l i : ℝ) * Real.log 2
        - ((k i : ℝ) * Real.log 3 + Real.log (a i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hc := chain_real h hi
    have hx := xm_cast h (hj i)
    have ha' : (0 : ℝ) < a ((i + 1) % m) := by exact_mod_cast (h.2 _ (hj i)).2.2.1
    have ha : (0 : ℝ) < a i := by exact_mod_cast (h.2 i hi).2.2.1
    have h1 : 1 + ε i = ((2 : ℝ) ^ k ((i + 1) % m) * a ((i + 1) % m) * 2 ^ l i) / ((3 : ℝ) ^ k i * a i) := by
      rw [hε]
      simp only
      rw [eq_div_iff (hA i hi).ne']
      rw [add_mul, div_mul_cancel₀ _ (hA i hi).ne']
      rw [hc, hx]
      ring
    rw [h1, Real.log_div (by positivity) (hA i hi).ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  have hsum : Lam m k l = ∑ i ∈ range m, Real.log (1 + ε i) := by
    have r1 : ∑ i ∈ range m, (k ((i + 1) % m) : ℝ) * Real.log 2 = ∑ i ∈ range m, (k i : ℝ) * Real.log 2 :=
      sum_rot_one m hm (fun j => (k j : ℝ) * Real.log 2)
    have r2 : ∑ i ∈ range m, Real.log (a ((i + 1) % m)) = ∑ i ∈ range m, Real.log (a i) :=
      sum_rot_one m hm (fun j => Real.log (a j))
    rw [Finset.sum_congr rfl hkey, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, r1, r2]
    unfold Lam Ksum Lsum
    push_cast
    rw [add_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    ring
  refine ⟨?_, ?_⟩
  · rw [hsum]
    apply Finset.sum_pos
    · intro i hi
      rw [Finset.mem_range] at hi
      exact Real.log_pos (by linarith [hεpos i hi])
    · exact ⟨0, Finset.mem_range.mpr hm⟩
  · rw [hsum]
    calc ∑ i ∈ range m, Real.log (1 + ε i) < ∑ i ∈ range m, ε i := by
          apply Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hm⟩
          intro i hi
          rw [Finset.mem_range] at hi
          have := Real.log_lt_sub_one_of_pos (by linarith [hεpos i hi] : 0 < 1 + ε i)
            (by linarith [hεpos i hi] : 1 + ε i ≠ 1)
          linarith
      _ ≤ ∑ i ∈ range m, 1 / (xm k a ((i + 1) % m) : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          have hc := chain_real h hi
          have hx1 := xm_pos h (hj i)
          have h2 := hl2 i hi
          rw [hε]
          simp only
          rw [div_le_div_iff₀ (hA i hi) (by linarith), hc]
          nlinarith
      _ = ∑ i ∈ range m, 1 / (xm k a i : ℝ) := by
          exact sum_rot_one m hm (fun j => 1 / (xm k a j : ℝ))

/-! ## `δ = log₂ 3` -/

theorem delta_eq_logb : δ = Real.logb 2 3 := rfl

theorem two_rpow_delta : (2 : ℝ) ^ δ = 3 := by
  rw [delta_eq_logb]
  exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

theorem one_lt_delta : 1 < δ := by
  unfold δ
  rw [lt_div_iff₀ (Real.log_pos (by norm_num)), one_mul]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- `3^{k_i} a_i ≤ (x_i + 1)^δ` (`x_i + 1 = 2^{k_i} a_i`, `2^δ = 3`, `a_i ≤ a_i^δ`). -/
theorem three_pow_le_rpow {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSol m k l a) {i : ℕ} (hi : i < m) :
    (3 : ℝ) ^ k i * a i ≤ ((xm k a i : ℝ) + 1) ^ δ := by
  have hx : (xm k a i : ℝ) + 1 = (2 : ℝ) ^ k i * a i := by rw [xm_cast h hi]; ring
  have ha : (1 : ℝ) ≤ a i := by exact_mod_cast (h.2 i hi).2.2.1
  rw [hx, Real.mul_rpow (by positivity) (by positivity)]
  have h2 : ((2 : ℝ) ^ k i) ^ δ = (3 : ℝ) ^ k i := by
    rw [← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      two_rpow_delta, Real.rpow_natCast]
  rw [h2]
  have h3 : (a i : ℝ) ≤ (a i : ℝ) ^ δ := by
    calc (a i : ℝ) = (a i : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (a i : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le ha one_lt_delta.le
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-! ## Lemma 6 -/

theorem lemma6_thm : lemma6 := by
  intro m k l a h i hi
  have hj : (i + 1) % m < m := Nat.mod_lt _ h.1
  have hc := chain_real h hi
  have hge := three_pow_le_rpow h hi
  have hl2 : (2 : ℝ) ≤ 2 ^ l i := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l i := pow_le_pow_right₀ (by norm_num) (h.2 i hi).2.1
  have hx1 := xm_pos h hj
  have hm := mul_le_mul_of_nonneg_right hl2 (by linarith : (0 : ℝ) ≤ (xm k a ((i + 1) % m) : ℝ))
  rw [lt_div_iff₀ (by norm_num)]
  linarith

/-! ## Lemma 7 -/

/-- `2 x_{i+1} ≤ (2 x_i)^δ`. -/
theorem two_x_succ_le {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSol m k l a) {i : ℕ} (hi : i < m) :
    2 * (xm k a ((i + 1) % m) : ℝ) ≤ (2 * (xm k a i : ℝ)) ^ δ := by
  have h6 := lemma6_thm m k l a h i hi
  have hx := xm_pos h hi
  have hle : ((xm k a i : ℝ) + 1) ^ δ ≤ (2 * (xm k a i : ℝ)) ^ δ :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith [one_lt_delta])
  rw [lt_div_iff₀ (by norm_num)] at h6
  linarith

theorem lemma7_min_thm : lemma7_min := by
  intro m k l a h i0 hi0
  have hm : 0 < m := h.1
  have hδ := one_lt_delta
  set w : ℕ → ℝ := fun j => Real.log (2 * (xm k a ((i0 + j) % m) : ℝ)) with hw
  have hxpos : ∀ i < m, (0 : ℝ) < 2 * (xm k a i : ℝ) := fun i hi => by linarith [xm_pos h hi]
  -- `w (j + 1) ≤ δ w j`
  have hrec : ∀ j, w (j + 1) ≤ δ * w j := by
    intro j
    have hij : (i0 + j) % m < m := Nat.mod_lt _ hm
    have hstep := two_x_succ_le h hij
    rw [Nat.mod_add_mod] at hstep
    simp only [hw]
    rw [show i0 + (j + 1) = i0 + j + 1 by omega, ← Real.log_rpow (hxpos _ hij)]
    exact Real.log_le_log (hxpos _ (Nat.mod_lt _ hm)) hstep
  have hpow : ∀ j, w j ≤ δ ^ j * w 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc w (j + 1) ≤ δ * w j := hrec j
        _ ≤ δ * (δ ^ j * w 0) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = δ ^ (j + 1) * w 0 := by ring
  -- `Σ w = Σ log (2 x_i) ≥ K log 2`
  have hlow : (Ksum m k : ℝ) * Real.log 2 ≤ ∑ j ∈ range m, w j := by
    have hr := sum_rot m hm (fun i => Real.log (2 * (xm k a i : ℝ))) i0
    simp only [hw]
    rw [hr, Ksum, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have hx := xm_pos h hi
    have hxc := xm_cast h hi
    have ha : (1 : ℝ) ≤ a i := by exact_mod_cast (h.2 i hi).2.2.1
    have h2k : (2 : ℝ) ^ k i ≤ 2 * (xm k a i : ℝ) := by
      have : (2 : ℝ) ^ k i ≤ (2 : ℝ) ^ k i * a i := le_mul_of_one_le_right (by positivity) ha
      linarith
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2k
  have hup : ∑ j ∈ range m, w j ≤ w 0 * ((δ ^ m - 1) / (δ - 1)) := by
    calc ∑ j ∈ range m, w j ≤ ∑ j ∈ range m, δ ^ j * w 0 := Finset.sum_le_sum (fun j _ => hpow j)
      _ = w 0 * ((δ ^ m - 1) / (δ - 1)) := by
          rw [← Finset.sum_mul, geom_sum_eq hδ.ne', mul_comm]
  have hA : 0 < δ - 1 := by linarith
  have hB : 0 < δ ^ m - 1 := by linarith [one_lt_pow₀ hδ hm.ne']
  have hw0 : Real.log 2 * ((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1)) ≤ w 0 := by
    calc Real.log 2 * ((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1))
        = ((Ksum m k : ℝ) * Real.log 2) * ((δ - 1) / (δ ^ m - 1)) := by ring
      _ ≤ (w 0 * ((δ ^ m - 1) / (δ - 1))) * ((δ - 1) / (δ ^ m - 1)) :=
          mul_le_mul_of_nonneg_right (hlow.trans hup) (div_nonneg hA.le hB.le)
      _ = w 0 := by field_simp
  have hw0' : w 0 = Real.log (2 * (xm k a i0 : ℝ)) := by
    simp only [hw]; rw [Nat.add_zero, Nat.mod_eq_of_lt hi0]
  rw [hw0'] at hw0
  rw [Real.rpow_sub_one (by norm_num), div_le_iff₀ (by norm_num), Real.rpow_def_of_pos (by norm_num)]
  calc Real.exp (Real.log 2 * ((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1)))
      ≤ Real.exp (Real.log (2 * (xm k a i0 : ℝ))) := Real.exp_le_exp.mpr hw0
    _ = (xm k a i0 : ℝ) * 2 := by rw [Real.exp_log (hxpos _ hi0)]; ring

theorem lemma7_thm : lemma7 := by
  intro m k l a h
  have hm : 0 < m := h.1
  set E : ℝ := (δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1) with hE
  have h4 := (lemma4_thm m k l a h).2
  have hterm : ∀ i ∈ range m, 1 / (xm k a i : ℝ) ≤ 2 * (2 : ℝ) ^ (-E) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h7 := lemma7_min_thm m k l a h i hi
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (E - 1) := Real.rpow_pos_of_pos (by norm_num) _
    calc 1 / (xm k a i : ℝ) ≤ 1 / (2 : ℝ) ^ (E - 1) := one_div_le_one_div_of_le hpos h7
      _ = 2 * (2 : ℝ) ^ (-E) := by
          rw [Real.rpow_sub_one (by norm_num), Real.rpow_neg (by norm_num)]
          field_simp
  calc Lam m k l < ∑ i ∈ range m, 1 / (xm k a i : ℝ) := h4
    _ ≤ ∑ i ∈ range m, 2 * (2 : ℝ) ^ (-E) := Finset.sum_le_sum hterm
    _ = 2 * (m : ℝ) * (2 : ℝ) ^ (-E) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Sdw2005
