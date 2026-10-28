import Mathlib
import Logs23.TwoLog_Enonces
import Logs23.Logs23_Enonces
import Logs23.Pont
import Logs23.Principal
import Logs23.Constantes

/-!
# Logs23 · proofs (step 2b): `two_log_lower`, `lam_lower_large`, `lam_lower`, and Steiner's theorem without hypothesis

The points: columns `j ↔ (r, s) ∈ Fin R × Fin S` (`R = 2^8 ν`, `S = 2^7 ν`), `r_j = r + 1`, `s_j = s`. For coprime
`b₁, b₂` the integers `r_j b₂ + s_j b₁` are distinct (`S ≤ b₂`), so `|V(ζ)| ≥ b₂^(−N²)`. Then `prop_main`,
`cond_P` and `final_ge` give `two_log_lower` in the coprime case; the general case follows by dividing by the
gcd and, for small reduced denominators, by the bridge (`bridge_gap`, `bridge_value`).
-/

namespace Logs23

open Finset Real Steiner

open scoped Nat

noncomputable section

/-! ## The grid of points -/

theorem NRS {ν : ℕ} (hν : 1 ≤ ν) : ν * (Kp ν + 1) = 2 ^ 8 * ν * (2 ^ 7 * ν) := by
  rw [Kp_succ hν]; ring

/-- Columns ↔ grid. -/
def cE {ν : ℕ} (hν : 1 ≤ ν) : Fin (ν * (Kp ν + 1)) ≃ Fin (2 ^ 8 * ν) × Fin (2 ^ 7 * ν) :=
  (finCongr (NRS hν)).trans finProdFinEquiv.symm

def rrG {ν : ℕ} (hν : 1 ≤ ν) (j : Fin (ν * (Kp ν + 1))) : ℕ := ((cE hν j).1 : ℕ) + 1
def ssG {ν : ℕ} (hν : 1 ≤ ν) (j : Fin (ν * (Kp ν + 1))) : ℕ := ((cE hν j).2 : ℕ)

theorem grid_injective {ν : ℕ} (hν : 1 ≤ ν) {b₁ b₂ : ℕ} (hcop : Nat.Coprime b₁ b₂) (hS : 2 ^ 7 * ν ≤ b₂) :
    Function.Injective fun j => rrG hν j * b₂ + ssG hν j * b₁ := by
  intro i j hij
  simp only at hij
  have hz : ((rrG hν i : ℤ) - rrG hν j) * b₂ = ((ssG hν j : ℤ) - ssG hν i) * b₁ := by
    have : ((rrG hν i * b₂ + ssG hν i * b₁ : ℕ) : ℤ) = ((rrG hν j * b₂ + ssG hν j * b₁ : ℕ) : ℤ) := by
      rw [hij]
    push_cast at this; linarith
  have hcop' : IsCoprime (b₂ : ℤ) b₁ := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hdvd : (b₂ : ℤ) ∣ ((ssG hν j : ℤ) - ssG hν i) := hcop'.dvd_of_dvd_mul_right ⟨(rrG hν i : ℤ) - rrG hν j, by rw [← hz]; ring⟩
  have hsj : ssG hν j < 2 ^ 7 * ν := (cE hν j).2.2
  have hsi : ssG hν i < 2 ^ 7 * ν := (cE hν i).2.2
  have hs : ssG hν j = ssG hν i := by
    have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)
    omega
  have hr : rrG hν i = rrG hν j := by
    rw [hs, sub_self, zero_mul] at hz
    have hb : (b₂ : ℤ) ≠ 0 := by
      have : 0 < b₂ := lt_of_lt_of_le (by positivity) hS
      exact_mod_cast this.ne'
    have := mul_eq_zero.mp hz
    rcases this with h | h
    · omega
    · exact absurd h hb
  apply (cE hν).injective
  simp only [rrG, ssG] at hs hr
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext hs.symm)

/-- `|V(ζ)| ≥ b^(−N²)` when `1 ≤ b` and `|ζ_j − ζ_i| ≥ 1/b` for `i ≠ j`. -/
theorem abs_vprod_ge {N : ℕ} (ζ : Fin N → ℝ) {b : ℝ} (hb : 1 ≤ b) (hsep : ∀ i j, i ≠ j → 1 / b ≤ |ζ j - ζ i|) :
    (1 / b) ^ (N ^ 2) ≤ |vprod ζ| := by
  have hb0 : 0 < 1 / b := by positivity
  have hb1 : 1 / b ≤ 1 := by rw [div_le_one (by linarith)]; exact hb
  rw [vprod, Finset.abs_prod]
  calc (1 / b) ^ (N ^ 2) = ∏ _i : Fin N, (1 / b) ^ N := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, sq]
    _ ≤ ∏ i : Fin N, |∏ j ∈ Ioi i, (ζ j - ζ i)| := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
        rw [Finset.abs_prod]
        calc (1 / b) ^ N ≤ (1 / b) ^ (Ioi i).card := by
              apply pow_le_pow_of_le_one hb0.le hb1
              calc (Ioi i).card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
                _ = N := by simp
          _ = ∏ _j ∈ Ioi i, 1 / b := (Finset.prod_const _).symm
          _ ≤ ∏ j ∈ Ioi i, |ζ j - ζ i| :=
              Finset.prod_le_prod₀ (fun j _ => hb0.le) fun j hj => hsep i j (ne_of_lt (Finset.mem_Ioi.mp hj))

/-! ## The coprime case -/

theorem b1_lt {b₁ b₂ : ℕ} (hb : 4 ≤ b₂) (hΛ : |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3| < 1) :
    b₁ < 2 * b₂ := by
  by_contra h
  rw [not_lt] at h
  have h' : (2 * b₂ : ℝ) ≤ b₁ := by exact_mod_cast h
  have hl : Real.log 3 ≤ 2 * Real.log 2 - 1 / 4 := by
    have h43 : (1 : ℝ) - 1 / (4 / 3) ≤ Real.log (4 / 3) := by
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
      simpa [one_div] using this
    have : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb' : (4 : ℝ) ≤ b₂ := by exact_mod_cast hb
  have : 1 ≤ (b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3 := by nlinarith
  have := le_abs_self ((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3)
  linarith

theorem two_pow_ge_sq {n : ℕ} (hn : 20 ≤ n) : 2 ^ 7 * n ^ 2 ≤ 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    have h2 : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]; ring
    rw [h2]
    calc 2 ^ 7 * (n + 1) ^ 2 ≤ 2 ^ 7 * (2 * n ^ 2) := Nat.mul_le_mul_left _ h1
      _ = 2 * (2 ^ 7 * n ^ 2) := by ring
      _ ≤ 2 * 2 ^ (n - 1) := Nat.mul_le_mul_left _ ih

theorem coprime_case {b₁ b₂ : ℕ} (hb₂ : 2 ^ 334 ≤ b₂) (hcop : Nat.Coprime b₁ b₂) :
    Real.exp (-(10 ^ 12 * ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5)) ≤
      |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3| := by
  set Λ := (b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3 with hΛ
  set ν := Nat.log 2 b₂ + 1 with hνdef
  by_cases hbig : 1 ≤ |Λ|
  · refine le_trans (le_of_lt ?_) hbig
    have : (0 : ℝ) < ((ν : ℕ) : ℝ) := by positivity
    have := pow_pos this 5
    calc Real.exp (-(10 ^ 12 * ((ν : ℕ) : ℝ) ^ 5)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  rw [not_le] at hbig
  have hb0 : 0 < b₂ := lt_of_lt_of_le (by positivity) hb₂
  have hν : 335 ≤ ν := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hb₂; omega
  have hν1 : 1 ≤ ν := by omega
  have hlt : (b₂ : ℝ) < 2 ^ ν := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b₂
    exact_mod_cast this
  have hge : 2 ^ (ν - 1) ≤ b₂ := by
    have := Nat.pow_log_le_self 2 hb0.ne'
    rwa [show ν - 1 = Nat.log 2 b₂ by omega]
  have hpow : 2 ^ 7 * ν ^ 2 ≤ b₂ := (two_pow_ge_sq (by omega)).trans hge
  have hS : 2 ^ 7 * ν ≤ b₂ := le_trans (Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero ν)) hpow
  have hb4 : 4 ≤ b₂ := le_trans (by simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 2 ≤ 334 by norm_num)) hb₂
  have hb1 : b₁ < 2 * b₂ := b1_lt hb4 hbig
  have hbr : (0 : ℝ) < b₂ := by exact_mod_cast hb0
  have hθ : (b₁ : ℝ) / b₂ < 2 := by
    rw [div_lt_iff₀ hbr]; exact_mod_cast hb1
  have hθ0 : (0 : ℝ) ≤ (b₁ : ℝ) / b₂ := by positivity
  -- the main inequality
  have hmain := prop_main (L := ν) (K := Kp ν) (rrG hν1) (ssG hν1) b₁ b₂ (2 ^ 7 * ν) hb0
    (fun j => by simp [rrG]) (fun j => (cE hν1 j).2.2) (grid_injective hν1 hcop hS)
    (zmax := 2 ^ 9 * ν) (lmax := ν * Real.log 2)
    (fun j => by
      have hr : ((rrG hν1 j : ℕ) : ℝ) ≤ 2 ^ 8 * ν := by
        have : rrG hν1 j ≤ 2 ^ 8 * ν := (cE hν1 j).1.2
        exact_mod_cast this
      have hs : ((ssG hν1 j : ℕ) : ℝ) ≤ 2 ^ 7 * ν := by
        have : ssG hν1 j ≤ 2 ^ 7 * ν := (cE hν1 j).2.2.le
        exact_mod_cast this
      have hs0 : (0 : ℝ) ≤ ssG hν1 j := Nat.cast_nonneg _
      have hm := mul_le_mul hs hθ.le hθ0 (by positivity)
      have : (2 : ℝ) ^ 9 * ν = 2 ^ 8 * ν + 2 ^ 7 * ν * 2 := by ring
      linarith)
    (fun l => by
      have : ((l : ℕ) : ℝ) + 1 ≤ ν := by exact_mod_cast l.2
      simp only [lam]
      exact mul_le_mul_of_nonneg_right this (Real.log_pos (by norm_num)).le)
    (by
      rw [abs_div, abs_of_pos hbr]
      have h7 : ((ν : ℝ) * ((2 ^ 7 * ν : ℕ) : ℝ)) ≤ b₂ := by
        have : ν * (2 ^ 7 * ν) ≤ b₂ := by
          calc ν * (2 ^ 7 * ν) = 2 ^ 7 * ν ^ 2 := by ring
            _ ≤ b₂ := hpow
        exact_mod_cast this
      rw [← mul_div_assoc, div_le_one hbr]
      have h0 : (0 : ℝ) ≤ (ν : ℝ) * ((2 ^ 7 * ν : ℕ) : ℝ) := by positivity
      calc (ν : ℝ) * ((2 ^ 7 * ν : ℕ) : ℝ) * |Λ| ≤ (ν : ℝ) * ((2 ^ 7 * ν : ℕ) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hbig.le h0
        _ ≤ b₂ := by linarith)
    (by norm_num : (1 : ℝ) ≤ 16) (cond_P hν hb0 hlt)
  -- the separation of the points
  have hsep : ∀ i j : Fin (ν * (Kp ν + 1)), i ≠ j →
      1 / (b₂ : ℝ) ≤ |((rrG hν1 j : ℝ) + ssG hν1 j * ((b₁ : ℝ) / b₂)) -
        ((rrG hν1 i : ℝ) + ssG hν1 i * ((b₁ : ℝ) / b₂))| := by
    intro i j hij
    have hne : ((rrG hν1 j * b₂ + ssG hν1 j * b₁ : ℕ) : ℤ) - ((rrG hν1 i * b₂ + ssG hν1 i * b₁ : ℕ) : ℤ) ≠ 0 := by
      intro h
      apply hij
      apply grid_injective hν1 hcop hS
      simp only
      exact_mod_cast (sub_eq_zero.mp h).symm
    have h1 := Int.one_le_abs hne
    have h1r : (1 : ℝ) ≤ |(((rrG hν1 j * b₂ + ssG hν1 j * b₁ : ℕ) : ℤ) -
        ((rrG hν1 i * b₂ + ssG hν1 i * b₁ : ℕ) : ℤ) : ℝ)| := by exact_mod_cast h1
    have heq : ((rrG hν1 j : ℝ) + ssG hν1 j * ((b₁ : ℝ) / b₂)) - ((rrG hν1 i : ℝ) + ssG hν1 i * ((b₁ : ℝ) / b₂)) =
        (((rrG hν1 j * b₂ + ssG hν1 j * b₁ : ℕ) : ℤ) - ((rrG hν1 i * b₂ + ssG hν1 i * b₁ : ℕ) : ℤ) : ℝ) / b₂ := by
      push_cast; field_simp
    rw [heq, abs_div, abs_of_pos hbr]
    exact div_le_div_of_nonneg_right h1r hbr.le
  have hV := abs_vprod_ge (fun j => (rrG hν1 j : ℝ) + ssG hν1 j * ((b₁ : ℝ) / b₂))
    (by exact_mod_cast hb0 : (1 : ℝ) ≤ b₂) hsep
  have hfin := final_ge hν hb0 hlt (T := Tlow (ν * (Kp ν + 1))
    (fun j => (rrG hν1 j : ℝ) + ssG hν1 j * ((b₁ : ℝ) / b₂))) (by
      rw [Tlow]
      have : 0 ≤ (∏ k : Fin (ν * (Kp ν + 1)), (1 / ((k : ℕ)! : ℝ))) * (Real.log 2 / 2) ^ tri (ν * (Kp ν + 1)) := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        exact mul_nonneg (Finset.prod_nonneg fun k _ => by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hV this)
  exact hfin.trans hmain

/-! ## `two_log_lower` -/

theorem two_log_lower_thm : two_log_lower := by
  intro b₁ b₂ hb₂
  have hb0 : 0 < b₂ := lt_of_lt_of_le (by positivity) hb₂
  have hg0 : 0 < Nat.gcd b₁ b₂ := Nat.gcd_pos_of_pos_right _ hb0
  obtain ⟨c₁, hc₁⟩ := Nat.gcd_dvd_left b₁ b₂
  obtain ⟨c₂, hc₂⟩ := Nat.gcd_dvd_right b₁ b₂
  have hcop : Nat.Coprime c₁ c₂ := by
    have := Nat.coprime_div_gcd_div_gcd (m := b₁) (n := b₂) hg0
    rwa [Nat.div_eq_of_eq_mul_right hg0 hc₁, Nat.div_eq_of_eq_mul_right hg0 hc₂] at this
  generalize Nat.gcd b₁ b₂ = g at hc₁ hc₂ hg0
  have hc₂0 : 0 < c₂ := by
    rcases Nat.eq_zero_or_pos c₂ with h | h
    · rw [h, mul_zero] at hc₂; omega
    · exact h
  -- `Λ = g Λ'`
  have hΛ : (b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3 = g * ((c₁ : ℝ) * Real.log 2 - (c₂ : ℝ) * Real.log 3) := by
    rw [hc₁, hc₂]; push_cast; ring
  have hgr : (1 : ℝ) ≤ g := by exact_mod_cast hg0
  have hge : |(c₁ : ℝ) * Real.log 2 - (c₂ : ℝ) * Real.log 3| ≤ |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3| := by
    rw [hΛ, abs_mul, abs_of_pos (show (0 : ℝ) < g by linarith)]
    exact le_mul_of_one_le_left (abs_nonneg _) hgr
  refine le_trans ?_ hge
  have hν0 : (0 : ℝ) < ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) := by positivity
  by_cases hsmall : c₂ < qBr'
  · -- the bridge
    have h1 := bridge_gap_thm c₂ (c₁ : ℤ) hc₂0 hsmall
    have h2 := bridge_value_thm
    push_cast at h1
    refine le_trans ?_ (h2.trans h1)
    -- `exp(−10^12 ν^5) ≤ 10^(−101)`
    have h101 : (101 : ℝ) * Real.log 10 ≤ 10 ^ 12 * ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5 := by
      have hl10 : Real.log 10 ≤ 10 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10); linarith
      have : (1 : ℝ) ≤ ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have := one_le_pow₀ this (n := 5)
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10)]
    calc Real.exp (-(10 ^ 12 * ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5)) ≤ Real.exp (-(101 * Real.log 10)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 10 ^ 101 := by
          rw [show -(101 * Real.log 10) = -Real.log (10 ^ 101) by rw [Real.log_pow]; push_cast; ring,
            Real.exp_neg, Real.exp_log (by positivity), one_div]
  · -- the coprime case
    rw [not_lt] at hsmall
    have hq : 2 ^ 334 ≤ qBr' := by unfold qBr'; decide +kernel
    have hc : 2 ^ 334 ≤ c₂ := hq.trans hsmall
    refine le_trans ?_ (coprime_case hc hcop)
    apply Real.exp_le_exp.mpr
    have hmono : Nat.log 2 c₂ ≤ Nat.log 2 b₂ := Nat.log_mono_right (by rw [hc₂]; exact Nat.le_mul_of_pos_left _ hg0)
    have : ((Nat.log 2 c₂ + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hmono
    have : ((Nat.log 2 c₂ + 1 : ℕ) : ℝ) ^ 5 ≤ ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by positivity) this 5
    linarith

/-! ## `lam_lower_large`, `lam_lower`, and Steiner's theorem without hypothesis -/

theorem pow5_le_two_pow {n : ℕ} (hn : 335 ≤ n) : 10 ^ 12 * n ^ 5 ≤ 2 ^ (n - 3) := by
  induction n, hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have h1 : (n + 1) ^ 5 ≤ 2 * n ^ 5 := by
      have hn' : (335 : ℝ) ≤ n := by exact_mod_cast hn
      have h0 : (0 : ℝ) ≤ n := by linarith
      have a5 : 335 * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
        have := mul_le_mul_of_nonneg_right hn' (pow_nonneg h0 4); nlinarith [this]
      have a4 : 335 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_right hn' (pow_nonneg h0 3); nlinarith [this]
      have a3 : 335 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_right hn' (pow_nonneg h0 2); nlinarith [this]
      have a2 : 335 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have e : ((n : ℝ) + 1) ^ 5 = (n : ℝ) ^ 5 + 5 * n ^ 4 + 10 * n ^ 3 + 10 * n ^ 2 + 5 * n + 1 := by ring
      have hr : ((n : ℝ) + 1) ^ 5 ≤ 2 * (n : ℝ) ^ 5 := by rw [e]; linarith
      exact_mod_cast hr
    have h2 : 2 ^ (n + 1 - 3) = 2 * 2 ^ (n - 3) := by
      rw [show n + 1 - 3 = (n - 3) + 1 by omega, pow_succ]; ring
    rw [h2]
    calc 10 ^ 12 * (n + 1) ^ 5 ≤ 10 ^ 12 * (2 * n ^ 5) := Nat.mul_le_mul_left _ h1
      _ = 2 * (10 ^ 12 * n ^ 5) := by ring
      _ ≤ 2 * 2 ^ (n - 3) := Nat.mul_le_mul_left _ ih

theorem lam_lower_large_thm : lam_lower_large := by
  intro k l hk
  have h := two_log_lower_thm (k + l) k hk
  set ν := Nat.log 2 k + 1 with hν
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk
  have hν335 : 335 ≤ ν := by have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hk; omega
  have hge : 2 ^ (ν - 1) ≤ k := by
    have := Nat.pow_log_le_self 2 hk0.ne'
    rwa [show ν - 1 = Nat.log 2 k by omega]
  have hLam : |((k + l : ℕ) : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3| = |Lam k l| := by rfl
  rw [hLam] at h
  refine le_trans ?_ h
  -- `1/(2^k − 1) ≤ exp(−10^12 ν^5)`, i.e. `exp(10^12 ν^5) ≤ 2^k − 1`
  have hpow := pow5_le_two_pow hν335
  have hpowr : (10 : ℝ) ^ 12 * (ν : ℝ) ^ 5 ≤ 2 ^ (ν - 3) := by exact_mod_cast hpow
  have hkr : (2 : ℝ) ^ (ν - 1) ≤ k := by exact_mod_cast hge
  have h2k : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k - 1 := by
    have : (1 : ℝ) ≤ 2 ^ (k - 1) := one_le_pow₀ (by norm_num)
    have h' : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    linarith
  have hexp : Real.exp (10 ^ 12 * (ν : ℝ) ^ 5) ≤ 2 ^ (k - 1) := by
    -- `10^12 ν^5 ≤ 2^(ν−3) ≤ (k − 1) log 2`
    have hlog2 := Real.log_two_gt_d9
    have h3 : (2 : ℝ) ^ (ν - 3) ≤ ((k - 1 : ℕ) : ℝ) * Real.log 2 := by
      have h4 : (2 : ℝ) ^ (ν - 1) = 4 * 2 ^ (ν - 3) := by
        rw [show ν - 1 = (ν - 3) + 2 by omega, pow_add]; ring
      have h5 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have h6 : (1 : ℝ) ≤ 2 ^ (ν - 3) := one_le_pow₀ (by norm_num)
      rw [h5]
      set X := (2 : ℝ) ^ (ν - 3) with hX
      have hk4 : 4 * X - 1 ≤ (k : ℝ) - 1 := by linarith
      have hl0 : (0 : ℝ) ≤ Real.log 2 := by linarith
      have hm := mul_le_mul_of_nonneg_right hk4 hl0
      have hm2 : (4 * X - 1) * 0.6931 ≤ (4 * X - 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    calc Real.exp (10 ^ 12 * (ν : ℝ) ^ 5) ≤ Real.exp (((k - 1 : ℕ) : ℝ) * Real.log 2) :=
          Real.exp_le_exp.mpr (hpowr.trans h3)
      _ = 2 ^ (k - 1) := by
          rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]; norm_cast
  have hpos : (0 : ℝ) < 2 ^ k - 1 := by
    have : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) (hexp.trans h2k)

theorem lam_lower_thm : lam_lower := by
  intro k l hk
  by_cases hsmall : k < qBr'
  · exact lam_lower_bridge_thm k l hk hsmall
  · rw [not_lt] at hsmall
    have hq : 2 ^ 334 ≤ qBr' := by unfold qBr'; decide +kernel
    exact lam_lower_large_thm k l (hq.trans hsmall)

theorem steiner_nh_thm : steiner_nh := (reduction_thm lam_lower_thm).1
theorem steiner_int_nh_thm : steiner_int_nh := (reduction_thm lam_lower_thm).2.1
theorem steiner_cycle_nh_thm : steiner_cycle_nh := (reduction_thm lam_lower_thm).2.2.1
theorem steiner_cycle_int_nh_thm : steiner_cycle_int_nh := (reduction_thm lam_lower_thm).2.2.2.1
theorem tstar_circuit_nh_thm : tstar_circuit_nh := (reduction_thm lam_lower_thm).2.2.2.2

end

end Logs23
