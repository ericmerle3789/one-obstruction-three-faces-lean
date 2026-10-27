import Mathlib
import Steiner.Steiner_Enonces
import Logs23.Logs23_Enonces
import Logs23.Encadrements

/-!
# Logs23 · proofs (2): the bridge

Write `(L, k) = a (pBr, qBr) + b (pBr', qBr')` in the basis of the two convergents, which is unimodular
(`pBr' qBr − pBr qBr' = 1`). Then `L log 2 − k log 3 = a e₁ + b e₂` with `e₁ = pBr log 2 − qBr log 3 < 0` and
`e₂ = pBr' log 2 − qBr' log 3 > 0`. For `0 < k < qBr'`, `a ≠ 0` and `a b ≤ 0`, so `b e₂` is zero or has the sign of
`a e₁`, and `|L log 2 − k log 3| ≥ |a e₁| ≥ |e₁|`. The two signs and `|e₁| ≥ 10^(−101)` come from the enclosures of
`Logs23/Encadrements.lean`, compared by the kernel.
-/

namespace Logs23

open Steiner

/-- If `e₁ < 0 < e₂`, `a ≠ 0` and `a b ≤ 0`, then `|e₁| ≤ |a e₁ + b e₂|`. -/
theorem abs_le_of_signs {e₁ e₂ : ℝ} (h₁ : e₁ < 0) (h₂ : 0 < e₂) {a b : ℤ} (ha : a ≠ 0) (hab : a * b ≤ 0) :
    |e₁| ≤ |(a : ℝ) * e₁ + (b : ℝ) * e₂| := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hb : 0 ≤ b := by
      by_contra hb
      rw [not_le] at hb
      nlinarith
    have ha' : (a : ℝ) ≤ -1 := by exact_mod_cast (by omega : a ≤ -1)
    have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
    rw [abs_of_neg h₁, abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hb : b ≤ 0 := by
      by_contra hb
      rw [not_le] at hb
      nlinarith
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast (by omega : 1 ≤ a)
    have hb' : (b : ℝ) ≤ 0 := by exact_mod_cast hb
    rw [abs_of_neg h₁, abs_of_nonpos (by nlinarith)]
    nlinarith

/-- The gap lemma for vectors of natural numbers `(p, q)`, `(p', q')` with `p' q − p q' = 1` whose linear forms
`p log 2 − q log 3 < 0 < p' log 2 − q' log 3` have opposite signs (`q ≥ 0` is used). -/
theorem gap_of_unimodular {p q p' q' : ℕ} (hu : (p' : ℤ) * q - p * q' = 1)
    (h₁ : (p : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3 < 0)
    (h₂ : 0 < (p' : ℝ) * Real.log 2 - (q' : ℝ) * Real.log 3)
    (k : ℕ) (L : ℤ) (hk : 0 < k) (hk' : k < q') :
    |(p : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3| ≤ |(L : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3| := by
  set a : ℤ := p' * k - L * q' with ha
  set b : ℤ := q * L - p * k with hb
  have hk_eq : (k : ℤ) = a * q + b * q' := by
    rw [ha, hb]
    linear_combination (-(k : ℤ)) * hu
  have hq' : (0 : ℤ) < q' := by exact_mod_cast (by omega : 0 < q')
  have hq : (0 : ℤ) ≤ q := by positivity
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
  have hk1 : (k : ℤ) < q' := by exact_mod_cast hk'
  -- `a ≠ 0`
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hk_eq
    rcases lt_trichotomy b 0 with hb0 | hb0 | hb0
    · nlinarith
    · rw [hb0, zero_mul] at hk_eq; omega
    · nlinarith
  -- `a b ≤ 0`
  have hab : a * b ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    rcases lt_or_gt_of_ne ha0 with han | hap
    · have hbn : b < 0 := by
        by_contra hb0; rw [not_lt] at hb0; nlinarith
      nlinarith
    · have hbp : 0 < b := by
        by_contra hb0; rw [not_lt] at hb0; nlinarith
      nlinarith
  have hcast : ((p' : ℝ) * q - p * q') = 1 := by exact_mod_cast hu
  have hid : (L : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 =
      (a : ℝ) * ((p : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3) +
        (b : ℝ) * ((p' : ℝ) * Real.log 2 - (q' : ℝ) * Real.log 3) := by
    rw [ha, hb]
    push_cast
    linear_combination (-((L : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3)) * hcast
  rw [hid]
  exact abs_le_of_signs h₁ h₂ ha0 hab

/-! ## The two convergents -/

theorem unimod_br : (pBr' : ℤ) * qBr - pBr * qBr' = 1 := by decide +kernel

/-- Rational form of `e₁_le`: the upper bound `pBr·L2hi − qBr·(L2lo + L32lo)` for `pBr log 2 − qBr log 3`
is `≤ −10^(−101)` (rational comparison by the kernel). -/
theorem e₁_rat : (pBr : ℚ) * L2hi - qBr * (L2lo + L32lo) ≤ -(1 / 10 ^ 101) := by decide +kernel

/-- Rational form of `e₂_pos`: the lower bound `pBr'·L2lo − qBr'·(L2hi + L32hi)` for `pBr' log 2 − qBr' log 3`
is `> 0` (rational comparison by the kernel). -/
theorem e₂_rat : 0 < (pBr' : ℚ) * L2lo - qBr' * (L2hi + L32hi) := by decide +kernel

theorem e₁_le : (pBr : ℝ) * Real.log 2 - (qBr : ℝ) * Real.log 3 ≤ -(1 / 10 ^ 101) := by
  obtain ⟨-, h2⟩ := log_two_bounds
  obtain ⟨h3, -⟩ := log_three_bounds
  have hr : ((pBr : ℚ) * L2hi - qBr * (L2lo + L32lo) : ℝ) ≤ ((-(1 / 10 ^ 101) : ℚ) : ℝ) := by
    exact_mod_cast e₁_rat
  push_cast at hr h3
  have hp : (0 : ℝ) ≤ pBr := by positivity
  have hq : (0 : ℝ) ≤ qBr := by positivity
  nlinarith

theorem e₂_pos : 0 < (pBr' : ℝ) * Real.log 2 - (qBr' : ℝ) * Real.log 3 := by
  obtain ⟨h1, -⟩ := log_two_bounds
  obtain ⟨-, h4⟩ := log_three_bounds
  have hr : ((0 : ℚ) : ℝ) < ((pBr' : ℚ) * L2lo - qBr' * (L2hi + L32hi) : ℝ) := by
    exact_mod_cast e₂_rat
  push_cast at hr h4
  have hp : (0 : ℝ) ≤ pBr' := by positivity
  have hq : (0 : ℝ) ≤ qBr' := by positivity
  nlinarith

theorem bridge_value_thm : bridge_value := by
  have h := e₁_le
  rw [bridge_value, abs_of_neg (by linarith)]
  linarith

theorem bridge_gap_thm : bridge_gap := by
  intro k L hk hk'
  have h₁ : (pBr : ℝ) * Real.log 2 - (qBr : ℝ) * Real.log 3 < 0 := by
    have := e₁_le
    have : (0 : ℝ) < 1 / 10 ^ 101 := by positivity
    linarith
  exact gap_of_unimodular unimod_br h₁ e₂_pos k L hk hk'

/-! ## The lower bound for `Λ` up to `qBr'` -/

theorem two_pow_big {k : ℕ} (hk : 20000 < k) : (10 : ℝ) ^ 101 ≤ (2 : ℝ) ^ k - 1 := by
  have h : (10 : ℕ) ^ 101 + 1 ≤ 2 ^ 400 := by decide +kernel
  have h' : (2 : ℕ) ^ 400 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : (10 : ℝ) ^ 101 + 1 ≤ (2 : ℝ) ^ k := by exact_mod_cast h.trans h'
  linarith

theorem lam_lower_bridge_thm : lam_lower_bridge := by
  intro k l hk hk'
  have hgap := bridge_gap_thm k ((k + l : ℕ) : ℤ) (by omega) hk'
  have hval := bridge_value_thm
  have hLam : |(((k + l : ℕ) : ℤ) : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3| = |Lam k l| := by
    unfold Lam; push_cast; ring_nf
  rw [hLam] at hgap
  have hb := two_pow_big hk
  have h10 : (0 : ℝ) < 10 ^ 101 := by positivity
  calc 1 / ((2 : ℝ) ^ k - 1) ≤ 1 / 10 ^ 101 := one_div_le_one_div_of_le h10 hb
    _ ≤ |Lam k l| := hval.trans hgap

end Logs23
