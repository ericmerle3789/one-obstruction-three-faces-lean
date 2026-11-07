import Mathlib
import Labo.HH1997c_Preuves

/-!
# LABO-COLLATZ · HH1997c_Demi · directeur (2026-11-07) — PROOF of `remark1_large`

Remark 1 of Halbeisen–Hungerbühler 1997 ends: for `l > 10³` the constant can be replaced by `1/2`, i.e.
`M_{l,n}/(n 3^n) ≤ 1/2` with `n = n(l)`. The paper's only indication is "Using similar arguments", presumably those
of the proof of Proposition 2, which ends with Lemma 3 and a geometric series; the route below uses these two tools. The constants 1/6 and 1/2
are stated, without proof, by K. Knight (preprint HAL hal-04261183v1, 2023, printed p. 7), only for
`l = ⌈n log₂ 3⌉` (1/2 for `l > 10³` is the paper's own).
Frozen statement: `remark1_large` of `Labo/HH1997c_Enonces.lean`, unchanged. Axiom check: `Labo/HH1997c_Demi_Axiomes.lean`
(output: `axioms/HH1997c_Demi_Axiomes.txt`).

Route:
1. closed form `M = Σ_{k<n} 2^{⌊kl/n⌋} 3^{n−1−k}`: Corollary 1 (`M_range_real`) reindexed by the positions of the ones
   (`j ↦ cl l n j` on the jumps, inverse `k ↦ ⌊kl/n⌋`); this closed form is known: HH Corollary 1 reindexed
   (Corollary 1 is reproduced in Cox–Ghosh–Sultanow 2021), and in this form in Knight 2023 (printed pp. 6–7) and in
   Fernández–Ibáñez, arXiv 2607.24844v1 (Theorem 7.3 and the proof of Theorem 8.2);
2. with `B = 2^{1/n}` and `y = B^l/3`: `M = 3^{n−1} Σ_k (B^{σ_k})⁻¹ y^k`, `σ_k = kl mod n`;
3. `τ(k) = σ_k + ⌊k/n'⌋` (`g = gcd(l,n)`, `n = g n'`) is injective on `[0,n)` and `τ(k) < σ_k + g`. Hence every suffix
   sum of `(B^{σ_k})⁻¹` is at most the same suffix sum of `B^g/B^{n−k}` (`sum_antitone_le`: an antitone sequence summed
   over `m` naturals is at most its sum over `0, …, m−1`), and `abel_suffix` (HH Lemma 3 in mirrored, suffix form,
   already used for Proposition 2 in `HH1997c_Preuves`) gives `Σ (B^{σ_k})⁻¹ y^k ≤ (B^g/2) Σ (By)^k`;
4. geometric sum and `log z ≤ z − 1`: `M ≤ (1/2)·n·3^n · 2^{1/n'} (t−1)/(3 log t)`, `t = 2^{l+1}/3^n ∈ ]2,6[`;
5. `n' ≥ 17` for `l > 1000` (otherwise `256·3^{n'} ≤ 243·2^{l'}` gives `g ≤ 21`, so `n ≤ 336` and `l ≤ 1000`), so
   `2^{1/n'} < 1.0418`; and `1.0418 (t−1) ≤ 3 log t` on `[2,6]` by concavity of `log`.
-/

namespace LaboHH

open Finset

/-! ## 1. Closed form of `M_{l,n}` -/

/-- The `k`-th one of `s̃(l,n)` sits at `⌊kl/n⌋`: there `⌈jn/l⌉` jumps from `k` to `k+1`. -/
lemma cl_at_pos {l n k : ℕ} (hl : 0 < l) (hn0 : 0 < n) (hnl : n ≤ l) :
    cl l n (k * l / n) = k ∧ cl l n (k * l / n + 1) = k + 1 := by
  have h1 : k * l / n * n ≤ k * l := Nat.div_mul_le_self _ _
  have h2 : k * l < k * l / n * n + n := Nat.lt_div_mul_add hn0
  have hA : cl l n (k * l / n) ≤ k := (cl_le_iff hl).2 h1
  have hB : k ≤ cl l n (k * l / n) := by
    by_contra hlt
    push Not at hlt
    have h3 : (cl l n (k * l / n) + 1) * l ≤ k * l := Nat.mul_le_mul_right l (Nat.succ_le_of_lt hlt)
    have h4 := le_cl_mul (n := n) hl (k * l / n)
    nlinarith
  have hC : cl l n (k * l / n + 1) ≤ k + 1 := by
    rw [cl_le_iff hl]
    nlinarith
  have hD : k + 1 ≤ cl l n (k * l / n + 1) := by
    by_contra hlt
    push Not at hlt
    have h5 : (k * l / n + 1) * n ≤ k * l := (cl_le_iff hl).1 (by omega)
    nlinarith
  exact ⟨le_antisymm hA hB, le_antisymm hC hD⟩

/-- At a jump `j` (a one of `s̃`), `j = ⌊⌈jn/l⌉ l / n⌋`. -/
lemma jump_inv {l n j : ℕ} (hl : 0 < l) (hn0 : 0 < n) (hj : cl l n j < cl l n (j + 1)) :
    cl l n j * l / n = j := by
  have hlo : j * n ≤ cl l n j * l := le_cl_mul hl j
  have hhi : cl l n j * l < (j + 1) * n := by
    by_contra hc
    push Not at hc
    have : cl l n (j + 1) ≤ cl l n j := (cl_le_iff hl).2 hc
    omega
  apply le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hn0).2 hhi)
  · exact (Nat.le_div_iff_mul_le hn0).2 hlo

/-- Closed form: `M_{l,n} = Σ_{k<n} 2^{⌊kl/n⌋} 3^{n−1−k}`. -/
lemma M_closed {l n : ℕ} (hl : 0 < l) (hn0 : 0 < n) (hnl : n ≤ l) :
    (M l n : ℝ) = ∑ k ∈ range n, (2 : ℝ) ^ (k * l / n) * (3 : ℝ) ^ (n - 1 - k) := by
  rw [M_range_real hl hnl]
  have hfilt : ∑ j ∈ range l, ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) * (2 : ℝ) ^ j * (3 : ℝ) ^ (n - cl l n (j + 1))
      = ∑ j ∈ (range l).filter (fun j => cl l n j < cl l n (j + 1)),
          (2 : ℝ) ^ j * (3 : ℝ) ^ (n - 1 - cl l n j) := by
    rw [sum_filter]
    refine sum_congr rfl fun j _ => ?_
    have hs := cl_succ_le hl hnl j
    have hm := cl_mono l n (Nat.le_succ j)
    split_ifs with h
    · have e1 : cl l n (j + 1) - cl l n j = 1 := by omega
      have e2 : n - cl l n (j + 1) = n - 1 - cl l n j := by omega
      rw [e1, e2]
      simp
    · have e1 : cl l n (j + 1) - cl l n j = 0 := by omega
      rw [e1]
      simp
  rw [hfilt]
  apply sum_nbij' (fun j => cl l n j) (fun k => k * l / n)
  · intro j hj
    simp only [mem_filter, mem_range] at hj ⊢
    have := cl_mono l n (show j + 1 ≤ l by omega)
    rw [cl_l hl] at this
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    obtain ⟨e1, e2⟩ := cl_at_pos (k := k) hl hn0 hnl
    refine ⟨?_, by omega⟩
    rw [Nat.div_lt_iff_lt_mul hn0]
    nlinarith
  · intro j hj
    simp only [mem_filter] at hj
    exact jump_inv hl hn0 hj.2
  · intro k _
    exact (cl_at_pos (k := k) hl hn0 hnl).1
  · intro j hj
    simp only [mem_filter] at hj
    rw [jump_inv hl hn0 hj.2]

/-! ## 2. Real form: `M = 3^{n−1} Σ_k (B^{σ_k})⁻¹ y^k` -/

lemma M_real_form {l n : ℕ} (hl : 0 < l) (hn0 : 0 < n) (hnl : n ≤ l) (B : ℝ) (hB : B ^ n = 2) (hB0 : 0 < B) :
    (M l n : ℝ) = 3 ^ (n - 1) * ∑ k ∈ range n, (B ^ (k * l % n))⁻¹ * (B ^ l / 3) ^ k := by
  rw [M_closed hl hn0 hnl, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  have hdm := Nat.div_add_mod (k * l) n
  have h2 : (2 : ℝ) ^ (k * l / n) = B ^ (k * l) / B ^ (k * l % n) := by
    rw [eq_div_iff (pow_ne_zero _ hB0.ne'), ← hB, ← pow_mul, ← pow_add, hdm]
  have h3 : (3 : ℝ) ^ (n - 1 - k) = 3 ^ (n - 1) / 3 ^ k := by
    rw [pow_sub₀ _ (by norm_num) (by omega)]
    ring
  rw [h2, h3, div_pow, ← pow_mul, mul_comm l k]
  have hBne : B ≠ 0 := hB0.ne'
  field_simp

/-! ## 3. The injection `τ` and the suffix domination -/

/-- An antitone sequence summed over `t` naturals is at most its sum over `0, …, t−1`. -/
lemma sum_antitone_le (a : ℕ → ℝ) (ha : Antitone a) (T : Finset ℕ) :
    ∑ j ∈ T, a j ≤ ∑ j ∈ range T.card, a j := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert m s hlt ih =>
    have hm : m ∉ s := fun h => lt_irrefl m (hlt m h)
    rw [sum_insert hm, card_insert_of_notMem hm, sum_range_succ]
    have hcard : s.card ≤ m := by
      calc s.card ≤ (range m).card := card_le_card (fun x hx => mem_range.2 (hlt x hx))
        _ = m := card_range m
    have := ha hcard
    linarith

lemma tau_lt {l n k : ℕ} (hn0 : 0 < n) (hk : k < n) : k / (n / Nat.gcd l n) < Nat.gcd l n := by
  have hg : 0 < Nat.gcd l n := Nat.gcd_pos_of_pos_right l hn0
  have hn' : 0 < n / Nat.gcd l n := Nat.div_pos (Nat.le_of_dvd hn0 (Nat.gcd_dvd_right l n)) hg
  rw [Nat.div_lt_iff_lt_mul hn', Nat.mul_div_cancel' (Nat.gcd_dvd_right l n)]
  exact hk

/-- `τ(k) = (kl mod n) + ⌊k/n'⌋` is injective on `[0, n)`. -/
lemma tau_inj {l n : ℕ} (hn0 : 0 < n) {k₁ k₂ : ℕ} (h₁ : k₁ < n) (h₂ : k₂ < n)
    (h : k₁ * l % n + k₁ / (n / Nat.gcd l n) = k₂ * l % n + k₂ / (n / Nat.gcd l n)) : k₁ = k₂ := by
  have hq₁ := tau_lt (l := l) hn0 h₁
  have hq₂ := tau_lt (l := l) hn0 h₂
  set g := Nat.gcd l n with hgdef
  set n' := n / g with hn'def
  set l' := l / g with hl'def
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right l hn0
  have hgn : g * n' = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right l n)
  have hgl : g * l' = l := Nat.mul_div_cancel' (Nat.gcd_dvd_left l n)
  have hcop : Nat.Coprime l' n' := Nat.coprime_div_gcd_div_gcd hg0
  obtain ⟨s₁, hs₁⟩ : g ∣ k₁ * l % n :=
    (Nat.dvd_mod_iff (Nat.gcd_dvd_right l n)).2 (Dvd.dvd.mul_left (Nat.gcd_dvd_left l n) k₁)
  obtain ⟨s₂, hs₂⟩ : g ∣ k₂ * l % n :=
    (Nat.dvd_mod_iff (Nat.gcd_dvd_right l n)).2 (Dvd.dvd.mul_left (Nat.gcd_dvd_left l n) k₂)
  rw [hs₁, hs₂] at h
  have hs : s₁ = s₂ := by
    have := congrArg (fun x => x / g) h
    simp only [Nat.mul_add_div hg0, Nat.div_eq_of_lt hq₁, Nat.div_eq_of_lt hq₂, add_zero] at this
    exact this
  have hq : k₁ / n' = k₂ / n' := by
    rw [hs] at h
    exact Nat.add_left_cancel h
  have hmod : k₁ * l ≡ k₂ * l [MOD n] := by
    show k₁ * l % n = k₂ * l % n
    rw [hs₁, hs₂, hs]
  have e2 : g * (k₁ * l') ≡ g * (k₂ * l') [MOD g * n'] := by
    rw [hgn, show g * (k₁ * l') = k₁ * l by rw [← hgl]; ring, show g * (k₂ * l') = k₂ * l by rw [← hgl]; ring]
    exact hmod
  have e3 : k₁ ≡ k₂ [MOD n'] :=
    Nat.ModEq.cancel_right_of_coprime hcop.symm (Nat.ModEq.mul_left_cancel' hg0.ne' e2)
  calc k₁ = n' * (k₁ / n') + k₁ % n' := (Nat.div_add_mod k₁ n').symm
    _ = n' * (k₂ / n') + k₂ % n' := by rw [hq, show k₁ % n' = k₂ % n' from e3]
    _ = k₂ := Nat.div_add_mod k₂ n'

/-- Suffix domination: `Σ_{K ≤ k < n} (B^{σ_k})⁻¹ ≤ Σ_{K ≤ k < n} B^g / B^{n−k}`. -/
lemma suffix_dom {l n : ℕ} (hn0 : 0 < n) (B : ℝ) (hB1 : 1 ≤ B) (K : ℕ) :
    ∑ k ∈ Ico K n, (B ^ (k * l % n))⁻¹ ≤ ∑ k ∈ Ico K n, B ^ Nat.gcd l n / B ^ (n - k) := by
  set g := Nat.gcd l n with hgdef
  set a : ℕ → ℝ := fun j => B ^ g / B ^ (j + 1) with hadef
  have hB0 : 0 < B := by linarith
  have hanti : Antitone a := by
    intro i j hij
    simp only [hadef]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ hB1 (by omega)
  set τ : ℕ → ℕ := fun k => k * l % n + k / (n / g) with hτdef
  have hterm : ∀ k ∈ Ico K n, (B ^ (k * l % n))⁻¹ ≤ a (τ k) := by
    intro k hk
    have hk' := (mem_Ico.mp hk).2
    have hq : k / (n / g) < g := tau_lt (l := l) hn0 hk'
    simp only [hadef, hτdef]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
    exact pow_le_pow_right₀ hB1 (by omega)
  have hinj : Set.InjOn τ (Ico K n : Set ℕ) := fun x hx y hy hxy =>
    tau_inj hn0 (mem_Ico.mp (mem_coe.mp hx)).2 (mem_Ico.mp (mem_coe.mp hy)).2 hxy
  calc ∑ k ∈ Ico K n, (B ^ (k * l % n))⁻¹ ≤ ∑ k ∈ Ico K n, a (τ k) := sum_le_sum hterm
    _ = ∑ j ∈ (Ico K n).image τ, a j := (sum_image hinj).symm
    _ ≤ ∑ j ∈ range ((Ico K n).image τ).card, a j := sum_antitone_le a hanti _
    _ = ∑ j ∈ range (n - K), a j := by rw [card_image_of_injOn hinj, Nat.card_Ico]
    _ = ∑ j ∈ range (n - K), a (n - K - 1 - j) := (sum_range_reflect a (n - K)).symm
    _ = ∑ k ∈ Ico K n, B ^ g / B ^ (n - k) := by
        rw [sum_Ico_eq_sum_range]
        refine sum_congr rfl fun i hi => ?_
        have hi' := mem_range.mp hi
        simp only [hadef]
        rw [show n - K - 1 - i + 1 = n - (K + i) by omega]

/-! ## 4. Numerical facts -/

/-- `1.0418 (t − 1) ≤ 3 log t` on `[2, 6]` (concavity of `log`, values at `2` and `6`). -/
lemma log_bound (t : ℝ) (ht2 : 2 ≤ t) (ht6 : t ≤ 6) : 1.0418 * (t - 1) ≤ 3 * Real.log t := by
  have hl2 := Real.log_two_gt_d9
  have hl3 : 19 * Real.log 2 < 12 * Real.log 3 := by
    have h : ((2 : ℝ) ^ 19) < 3 ^ 12 := by norm_num
    have := Real.log_lt_log (by positivity) h
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have ha : 0 ≤ (6 - t) / 4 := by linarith
  have hb : 0 ≤ (t - 2) / 4 := by linarith
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (6 : ℝ) ∈ Set.Ioi 0 by norm_num) ha hb (by ring)
  simp only [smul_eq_mul] at hconc
  rw [show (6 - t) / 4 * 2 + (t - 2) / 4 * 6 = t by ring] at hconc
  have h2' : 1.0418 ≤ 3 * Real.log 2 := by linarith
  have h6' : 5.209 ≤ 3 * Real.log 6 := by rw [hl6]; linarith
  nlinarith [mul_le_mul_of_nonneg_left h2' ha, mul_le_mul_of_nonneg_left h6' hb]

lemma small_ratio : ∀ a < 17, ∀ b < 34, 3 ^ a < 2 ^ b → 256 * 3 ^ a ≤ 243 * 2 ^ b := by decide +kernel

lemma ratio_ge {a b : ℕ} (ha : a ≤ 16) (h : 3 ^ a < 2 ^ b) : 256 * 3 ^ a ≤ 243 * 2 ^ b := by
  rcases Nat.lt_or_ge b 34 with hb | hb
  · exact small_ratio a (by omega) b hb h
  · have h1 : 3 ^ a ≤ 3 ^ 16 := Nat.pow_le_pow_right (by norm_num) ha
    have h2 : 2 ^ 34 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    have h3 : 256 * 3 ^ 16 ≤ 243 * 2 ^ 34 := by norm_num
    calc 256 * 3 ^ a ≤ 256 * 3 ^ 16 := Nat.mul_le_mul_left _ h1
      _ ≤ 243 * 2 ^ 34 := h3
      _ ≤ 243 * 2 ^ b := Nat.mul_le_mul_left _ h2

/-- For `l > 1000`, `n' = n / gcd(l, n) ≥ 17`. -/
lemma nprime_ge {l n : ℕ} (hl : 1000 < l) (hn0 : 0 < n) (h1 : 3 ^ n < 2 ^ l) (h2 : 2 ^ l < 3 ^ (n + 1)) :
    17 ≤ n / Nat.gcd l n := by
  have hg0 : 0 < Nat.gcd l n := Nat.gcd_pos_of_pos_right l hn0
  have hgn : Nat.gcd l n * (n / Nat.gcd l n) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right l n)
  have hgl : Nat.gcd l n * (l / Nat.gcd l n) = l := Nat.mul_div_cancel' (Nat.gcd_dvd_left l n)
  set g := Nat.gcd l n with hgdef
  set n' := n / g with hn'def
  set l' := l / g with hl'def
  by_contra hlt
  push Not at hlt
  have h1' : 3 ^ n' < 2 ^ l' := by
    have : (3 ^ n') ^ g < (2 ^ l') ^ g := by
      rw [← pow_mul, ← pow_mul, mul_comm n' g, mul_comm l' g, hgn, hgl]
      exact h1
    exact lt_of_pow_lt_pow_left₀ g (Nat.zero_le _) this
  have hr := ratio_ge (by omega : n' ≤ 16) h1'
  have hpow : (256 * 3 ^ n') ^ g ≤ (243 * 2 ^ l') ^ g := Nat.pow_le_pow_left hr g
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm n' g, mul_comm l' g, hgn, hgl] at hpow
  have hg21 : g ≤ 21 := by
    by_contra hg
    push Not at hg
    have hsplit : ∀ c : ℕ, c ^ g = c ^ 22 * c ^ (g - 22) := fun c => by
      rw [← pow_add]
      congr 1
      omega
    have hA : 3 * 243 ^ 22 ≤ 256 ^ 22 := by norm_num
    have hB' : 243 ^ (g - 22) ≤ 256 ^ (g - 22) := Nat.pow_le_pow_left (by norm_num) _
    have h3 : 3 * 243 ^ g ≤ 256 ^ g := by
      calc 3 * 243 ^ g = 3 * 243 ^ 22 * 243 ^ (g - 22) := by rw [hsplit 243]; ring
        _ ≤ 256 ^ 22 * 256 ^ (g - 22) := Nat.mul_le_mul hA hB'
        _ = 256 ^ g := (hsplit 256).symm
    have h4 : 243 ^ g * 2 ^ l < 243 ^ g * 3 ^ (n + 1) := Nat.mul_lt_mul_of_pos_left h2 (by positivity)
    have h6 : 3 * 243 ^ g * 3 ^ n ≤ 256 ^ g * 3 ^ n := Nat.mul_le_mul_right _ h3
    have h7 : 243 ^ g * 3 ^ (n + 1) = 3 * 243 ^ g * 3 ^ n := by ring
    have : 256 ^ g * 3 ^ n < 256 ^ g * 3 ^ n := by
      calc 256 ^ g * 3 ^ n ≤ 243 ^ g * 2 ^ l := hpow
        _ < 243 ^ g * 3 ^ (n + 1) := h4
        _ = 3 * 243 ^ g * 3 ^ n := h7
        _ ≤ 256 ^ g * 3 ^ n := h6
    exact lt_irrefl _ this
  have hn336 : n ≤ 336 := by
    rw [← hgn]
    exact le_trans (Nat.mul_le_mul hg21 (by omega : n' ≤ 16)) (by norm_num)
  have h3 : 2 ^ l < 2 ^ 1001 := by
    calc 2 ^ l < 3 ^ (n + 1) := h2
      _ ≤ 3 ^ 337 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ 1001 := by decide +kernel
  have := (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).mp h3
  omega

/-! ## 5. The bound -/

lemma half_core {l n : ℕ} (hl : 0 < l) (hn0 : 0 < n) (hnl : n ≤ l) (h1 : 3 ^ n < 2 ^ l)
    (h2 : 2 ^ l < 3 ^ (n + 1)) (hn' : 17 ≤ n / Nat.gcd l n) :
    (M l n : ℝ) ≤ 1 / 2 * (n * 3 ^ n) := by
  have hgn : Nat.gcd l n * (n / Nat.gcd l n) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right l n)
  set g := Nat.gcd l n with hgdef
  set n' := n / g with hn'def
  set B : ℝ := (2 : ℝ) ^ ((n : ℝ)⁻¹) with hBdef
  have hB : B ^ n = 2 := Real.rpow_inv_natCast_pow (by norm_num) hn0.ne'
  have hB1 : 1 ≤ B := Real.one_le_rpow (by norm_num) (by positivity)
  have hB0 : 0 < B := by linarith
  have hBne : B ≠ 0 := hB0.ne'
  set y : ℝ := B ^ l / 3 with hydef
  have h1R : (3 : ℝ) ^ n < 2 ^ l := by exact_mod_cast h1
  have h2R : (2 : ℝ) ^ l < 3 ^ (n + 1) := by exact_mod_cast h2
  have h3pos : (0 : ℝ) < 3 ^ n := by positivity
  have hyn : y ^ n = 2 ^ l / 3 ^ n := by
    rw [hydef, div_pow, ← pow_mul, mul_comm l n, pow_mul, hB]
  have hy0 : 0 < y := by rw [hydef]; positivity
  have hy1 : 1 < y := by
    by_contra hy
    push Not at hy
    have h := pow_le_one₀ (n := n) hy0.le hy
    rw [hyn, div_le_one h3pos] at h
    linarith
  -- Abel with the suffix domination
  have habel := abel_suffix n (fun k => (B ^ (k * l % n))⁻¹) (fun k => B ^ g / B ^ (n - k)) (fun k => y ^ k)
    (fun k => pow_le_pow_right₀ hy1.le (Nat.le_succ k)) (by simp) (fun K _ => suffix_dom hn0 B hB1 K)
  -- geometric sum
  set z : ℝ := B * y with hzdef
  have hz1 : 1 < z := by rw [hzdef]; nlinarith
  have hd : ∑ k ∈ range n, B ^ g / B ^ (n - k) * y ^ k = B ^ g / 2 * ∑ k ∈ range n, z ^ k := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    have e : B ^ (n - k) * B ^ k = 2 := by rw [← pow_add, Nat.sub_add_cancel hk'.le, hB]
    have e' : B ^ g / B ^ (n - k) = B ^ g / 2 * B ^ k := by
      rw [← e]
      field_simp
    rw [e', hzdef, mul_pow]
    ring
  have hzn : z ^ n = 2 * (2 ^ l / 3 ^ n) := by rw [hzdef, mul_pow, hB, hyn]
  have hgeom : ∑ k ∈ range n, z ^ k = (z ^ n - 1) / (z - 1) := geom_sum_eq hz1.ne' n
  set t : ℝ := 2 * (2 ^ l / 3 ^ n) with htdef
  have ht2 : 2 < t := by
    have : 1 < (2 : ℝ) ^ l / 3 ^ n := (one_lt_div h3pos).2 h1R
    rw [htdef]
    linarith
  have ht6 : t < 6 := by
    have : (2 : ℝ) ^ l / 3 ^ n < 3 := by
      rw [div_lt_iff₀ h3pos]
      have : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
      linarith
    rw [htdef]
    linarith
  have hlogz : Real.log t = n * Real.log z := by rw [← hzn, Real.log_pow]
  have hlogz_le : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hgeom_le : ∑ k ∈ range n, z ^ k ≤ n * (t - 1) / Real.log t := by
    rw [hgeom, hzn, div_le_div_iff₀ (by linarith) hlogt, hlogz]
    have h0 : (0 : ℝ) ≤ n * (t - 1) := by
      have : (0 : ℝ) ≤ t - 1 := by linarith
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogz_le h0]
  -- `2^{1/n'} < 1.0418`
  have hβn : (B ^ g) ^ n' = 2 := by rw [← pow_mul, hgn, hB]
  have hβ1 : 1 ≤ B ^ g := one_le_pow₀ hB1
  have hβ : B ^ g < 1.0418 := by
    by_contra hc
    push Not at hc
    have h17 : (1.0418 : ℝ) ^ 17 ≤ (B ^ g) ^ 17 := pow_le_pow_left₀ (by norm_num) hc 17
    have h17' : (B ^ g) ^ 17 ≤ (B ^ g) ^ n' := pow_le_pow_right₀ hβ1 hn'
    have hc17 : (2 : ℝ) < 1.0418 ^ 17 := by norm_num
    linarith
  have hnum := log_bound t ht2.le ht6.le
  have key : B ^ g * (t - 1) ≤ 3 * Real.log t := by
    have : B ^ g * (t - 1) ≤ 1.0418 * (t - 1) :=
      mul_le_mul_of_nonneg_right hβ.le (by linarith)
    linarith
  have h3n : (3 : ℝ) ^ n = 3 * 3 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hratio : B ^ g * (t - 1) / Real.log t ≤ 3 := (div_le_iff₀ hlogt).2 (by linarith)
  calc (M l n : ℝ) = 3 ^ (n - 1) * ∑ k ∈ range n, (B ^ (k * l % n))⁻¹ * y ^ k :=
        M_real_form hl hn0 hnl B hB hB0
    _ ≤ 3 ^ (n - 1) * ∑ k ∈ range n, B ^ g / B ^ (n - k) * y ^ k :=
        mul_le_mul_of_nonneg_left habel (by positivity)
    _ = 3 ^ (n - 1) * (B ^ g / 2 * ∑ k ∈ range n, z ^ k) := by rw [hd]
    _ ≤ 3 ^ (n - 1) * (B ^ g / 2 * (n * (t - 1) / Real.log t)) := by gcongr
    _ = 3 ^ (n - 1) * n / 2 * (B ^ g * (t - 1) / Real.log t) := by ring
    _ ≤ 3 ^ (n - 1) * n / 2 * 3 := by gcongr
    _ = 1 / 2 * (n * 3 ^ n) := by rw [h3n]; ring

/-- **Remark 1, `1/2` for `l > 10³`** (Halbeisen–Hungerbühler 1997, stated there without proof). -/
theorem remark1_large_thm : remark1_large := by
  intro l hl
  have hl0 : 0 < l := by omega
  have hn0 : 0 < nOf l := nOf_pos (by omega)
  have hnl := nOf_le l
  obtain ⟨h1, h2⟩ := nOf_spec_thm l hl0
  have hden : (0 : ℝ) < nOf l * 3 ^ nOf l := mul_pos (by exact_mod_cast hn0) (by positivity)
  rw [div_le_iff₀ hden]
  exact half_core hl0 hn0 hnl h1 h2 (nprime_ge hl hn0 h1 h2)

end LaboHH
