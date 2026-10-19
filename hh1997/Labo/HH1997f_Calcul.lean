import Mathlib
import Labo.HH1997f_Mots

/-!
# LABO-COLLATZ · HH1997f · formaliste (2026-10-19) — the continued-fraction words and the kernel computations

Part 2 of the proofs of `Labo/HH1997f_Enonces.lean`.

* `cfP`, `cfW`: the pairs `(p_k, q_k)` and the words `W_k = s̃(p_k, q_k)` built along the continued fraction of
  `log₂ 3` (`W₋₁ = 0`, `W₀ = 1`, `W_{k+1} = W_k^{a_{k+1}} W_{k−1}` for `k` even, `W_{k−1} W_k^{a_{k+1}}` for `k` odd);
  `cf_inv`: `W_k = s̃(p_k, q_k)` for every `k` (from `stilde_append_thm`).
* `cfT`: the same recursion on triples `(length, number of 1s, ϕ)` (eq. (4)); the kernel evaluates it up to
  `k = 13` (`p₁₃ = 301 994`): its integers have at most 302 010 bits, and the enclosure checks below (×2^128) at most 302 138 bits.  (The kernel refuses integers above
  `2^24` bits by default; `2^{p₁₅}` would have 17 087 916 bits.  Probe recorded in the report.)
* 128-bit enclosures of `f = ϕ/2^l` and `g = 3^n/2^l` for `W₁₂ = s̃(176 251, 111 202)` and
  `W₁₃ = s̃(301 994, 190 537)`, checked by `decide +kernel` (GMP arithmetic, no `native_decide`).
-/

namespace LaboHH

open LaboBP

/-! ## Words along the continued fraction -/

/-- `a_{k+1}` for `k = 0 … 12`: `log₂ 3 = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, …]`. -/
def aq (k : ℕ) : ℕ := [1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1].getD k 1

/-- `((p_{k−1}, q_{k−1}), (p_k, q_k))` as `((l, n), (l, n))`. -/
def cfP : ℕ → (ℕ × ℕ) × (ℕ × ℕ)
  | 0 => ((1, 0), (1, 1))
  | k + 1 => let p := cfP k; (p.2, (aq k * p.2.1 + p.1.1, aq k * p.2.2 + p.1.2))

/-- `(W_{k−1}, W_k)`. -/
def cfW : ℕ → List Bool × List Bool
  | 0 => ([false], [true])
  | k + 1 => let p := cfW k;
    (p.2, if k % 2 = 0 then wpow p.2 (aq k) ++ p.1 else p.1 ++ wpow p.2 (aq k))

lemma cfP_succ (k : ℕ) :
    cfP (k + 1) = ((cfP k).2, (aq k * (cfP k).2.1 + (cfP k).1.1, aq k * (cfP k).2.2 + (cfP k).1.2)) := rfl

lemma cfW_succ (k : ℕ) : cfW (k + 1) = ((cfW k).2,
    if k % 2 = 0 then wpow (cfW k).2 (aq k) ++ (cfW k).1 else (cfW k).1 ++ wpow (cfW k).2 (aq k)) := rfl

/-- The invariant: `W_{k−1} = s̃(p_{k−1}, q_{k−1})`, `W_k = s̃(p_k, q_k)`, and the determinant `±1`. -/
def CfInv (k : ℕ) : Prop :=
  0 < (cfP k).1.1 ∧ 0 < (cfP k).2.1 ∧
  stilde (cfP k).1.1 (cfP k).1.2 = (cfW k).1 ∧ stilde (cfP k).2.1 (cfP k).2.2 = (cfW k).2 ∧
  (if k % 2 = 0 then (cfP k).2.2 * (cfP k).1.1 = (cfP k).1.2 * (cfP k).2.1 + 1
    else (cfP k).1.2 * (cfP k).2.1 = (cfP k).2.2 * (cfP k).1.1 + 1)

lemma cf_inv (k : ℕ) : CfInv k := by
  induction k with
  | zero =>
    refine ⟨by simp [cfP], by simp [cfP], ?_, ?_, by simp [cfP]⟩
    · simp [cfP, cfW, stilde, cl]
    · simp [cfP, cfW, stilde, cl]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    unfold CfInv
    rw [cfP_succ, cfW_succ]
    simp only
    set lu := (cfP k).1.1
    set nu := (cfP k).1.2
    set lv := (cfP k).2.1
    set nv := (cfP k).2.2
    set a := aq k
    by_cases hk : k % 2 = 0
    · have hk' : ¬ (k + 1) % 2 = 0 := by omega
      simp only [hk, hk', ↓reduceIte] at h5 ⊢
      refine ⟨h2, by positivity, h4, ?_, ?_⟩
      · rw [← h4, ← h3]; exact stilde_wpow_append h1 h2 h5 a
      · nlinarith
    · have hk' : (k + 1) % 2 = 0 := by omega
      simp only [hk, hk', ↓reduceIte] at h5 ⊢
      refine ⟨h2, by positivity, h4, ?_, ?_⟩
      · rw [← h4, ← h3, show a * lv + lu = lu + a * lv by ring, show a * nv + nu = nu + a * nv by ring]
        exact stilde_append_wpow h1 h2 h5 a
      · nlinarith

lemma cfP_13 : cfP 13 = ((176251, 111202), (301994, 190537)) := by decide

lemma W12_eq : stilde 176251 111202 = (cfW 13).1 := by
  have := (cf_inv 13).2.2.1; rwa [cfP_13] at this

lemma W13_eq : stilde 301994 190537 = (cfW 13).2 := by
  have := (cf_inv 13).2.2.2.1; rwa [cfP_13] at this

/-! ## The same recursion on triples `(length, number of 1s, ϕ)` -/

/-- Concatenation of triples, eq. (4). -/
def tapp (a b : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (a.1 + b.1, a.2.1 + b.2.1, 3 ^ b.2.1 * a.2.2 + 2 ^ a.1 * b.2.2)

/-- `k`-th power of a triple. -/
def tpow (t : ℕ × ℕ × ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | k + 1 => tapp (tpow t k) t

/-- The triple of a word. -/
def trip (w : List Bool) : ℕ × ℕ × ℕ := (w.length, w.count true, phi w)

lemma trip_append (u v : List Bool) : trip (u ++ v) = tapp (trip u) (trip v) := by
  simp only [trip, tapp, List.length_append, List.count_append, eq4_thm u v]

lemma trip_wpow (w : List Bool) (k : ℕ) : trip (wpow w k) = tpow (trip w) k := by
  induction k with
  | zero => simp [wpow, trip, tpow, phi, phiRev]
  | succ k ih => rw [wpow_succ', trip_append, ih, tpow]

/-- `(trip W_{k−1}, trip W_k)`, computed without building the words. -/
def cfT : ℕ → (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)
  | 0 => ((1, 0, 0), (1, 1, 1))
  | k + 1 => let p := cfT k;
    (p.2, if k % 2 = 0 then tapp (tpow p.2 (aq k)) p.1 else tapp p.1 (tpow p.2 (aq k)))

lemma cfT_eq (k : ℕ) : cfT k = (trip (cfW k).1, trip (cfW k).2) := by
  induction k with
  | zero => simp [cfT, cfW, trip, phi, phiRev]
  | succ k ih =>
    show ((cfT k).2, if k % 2 = 0 then tapp (tpow (cfT k).2 (aq k)) (cfT k).1
        else tapp (cfT k).1 (tpow (cfT k).2 (aq k))) = _
    rw [cfW_succ, ih]
    split_ifs <;> simp [trip_append, trip_wpow]

lemma phi_W12 : phi (stilde 176251 111202) = (cfT 13).1.2.2 := by rw [cfT_eq, W12_eq]; simp only [trip]

lemma phi_W13 : phi (stilde 301994 190537) = (cfT 13).2.2.2 := by rw [cfT_eq, W13_eq]; simp only [trip]

/-! ## Kernel computations (GMP), 128-bit enclosures -/

lemma k_g12 : 340283592012203493962236082130303380839 * 2 ^ 176251 ≤ 3 ^ 111202 * 2 ^ 128 ∧
    3 ^ 111202 * 2 ^ 128 < (340283592012203493962236082130303380839 + 1) * 2 ^ 176251 := by
  decide +kernel

lemma k_g13 : 340282344970173444125912616851586510561 * 2 ^ 301994 ≤ 3 ^ 190537 * 2 ^ 128 ∧
    3 ^ 190537 * 2 ^ 128 < (340282344970173444125912616851586510561 + 1) * 2 ^ 301994 := by
  decide +kernel

lemma k_f12 : 9098660640394714237041777518385491641289669 * 2 ^ 176251 ≤ (cfT 13).1.2.2 * 2 ^ 128 ∧
    (cfT 13).1.2.2 * 2 ^ 128 < (9098660640394714237041777518385491641289669 + 1) * 2 ^ 176251 := by
  decide +kernel

lemma k_f13 : 15589882160217497337152154759217496172072404 * 2 ^ 301994 ≤ (cfT 13).2.2.2 * 2 ^ 128 ∧
    (cfT 13).2.2.2 * 2 ^ 128 < (15589882160217497337152154759217496172072404 + 1) * 2 ^ 301994 := by
  decide +kernel

/-! ## The enclosures in ℚ -/

lemma gw_stilde {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) : gw (stilde l n) = (3 : ℚ) ^ n / 2 ^ l := by
  unfold gw; rw [stilde_length, stilde_count hl hn]

lemma fw_stilde (l n : ℕ) : fw (stilde l n) = (phi (stilde l n) : ℚ) / 2 ^ l := by
  unfold fw; rw [stilde_length]

lemma gw_encl {l n G K : ℕ} (hl : 0 < l) (hn : n ≤ l) (h1 : G * 2 ^ l ≤ 3 ^ n * 2 ^ K)
    (h2 : 3 ^ n * 2 ^ K < (G + 1) * 2 ^ l) :
    (G : ℚ) / 2 ^ K ≤ gw (stilde l n) ∧ gw (stilde l n) < ((G : ℚ) + 1) / 2 ^ K := by
  rw [gw_stilde hl hn]
  have h1' : (G : ℚ) * 2 ^ l ≤ 3 ^ n * 2 ^ K := by exact_mod_cast h1
  have h2' : (3 : ℚ) ^ n * 2 ^ K < ((G : ℚ) + 1) * 2 ^ l := by exact_mod_cast h2
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith

lemma fw_encl {l n F K Φ : ℕ} (hΦ : phi (stilde l n) = Φ) (h1 : F * 2 ^ l ≤ Φ * 2 ^ K)
    (h2 : Φ * 2 ^ K < (F + 1) * 2 ^ l) :
    (F : ℚ) / 2 ^ K ≤ fw (stilde l n) ∧ fw (stilde l n) < ((F : ℚ) + 1) / 2 ^ K := by
  rw [fw_stilde, hΦ]
  have h1' : (F : ℚ) * 2 ^ l ≤ Φ * 2 ^ K := by exact_mod_cast h1
  have h2' : (Φ : ℚ) * 2 ^ K < ((F : ℚ) + 1) * 2 ^ l := by exact_mod_cast h2
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith

local notation "G12" => (340283592012203493962236082130303380839 : ℚ)
local notation "G13" => (340282344970173444125912616851586510561 : ℚ)
local notation "F12" => (9098660640394714237041777518385491641289669 : ℚ)
local notation "F13" => (15589882160217497337152154759217496172072404 : ℚ)


lemma g12_encl : G12 / 2 ^ 128 ≤ gw (stilde 176251 111202) ∧ gw (stilde 176251 111202) < (G12 + 1) / 2 ^ 128 := by
  have := gw_encl (l := 176251) (n := 111202) (G := 340283592012203493962236082130303380839) (K := 128)
    (by norm_num) (by norm_num) k_g12.1 k_g12.2
  exact_mod_cast this

lemma g13_encl : G13 / 2 ^ 128 ≤ gw (stilde 301994 190537) ∧ gw (stilde 301994 190537) < (G13 + 1) / 2 ^ 128 := by
  have := gw_encl (l := 301994) (n := 190537) (G := 340282344970173444125912616851586510561) (K := 128)
    (by norm_num) (by norm_num) k_g13.1 k_g13.2
  exact_mod_cast this

lemma f12_encl : F12 / 2 ^ 128 ≤ fw (stilde 176251 111202) ∧ fw (stilde 176251 111202) < (F12 + 1) / 2 ^ 128 := by
  have := fw_encl (l := 176251) (n := 111202) (F := 9098660640394714237041777518385491641289669) (K := 128)
    phi_W12 k_f12.1 k_f12.2
  exact_mod_cast this

lemma f13_encl : F13 / 2 ^ 128 ≤ fw (stilde 301994 190537) ∧ fw (stilde 301994 190537) < (F13 + 1) / 2 ^ 128 := by
  have := fw_encl (l := 301994) (n := 190537) (F := 15589882160217497337152154759217496172072404) (K := 128)
    phi_W13 k_f13.1 k_f13.2
  exact_mod_cast this

/-! ## The numerical inequalities (rational arithmetic, `norm_num`) -/

/-- `good(W₁₅)` with the upper enclosures (the Third step). -/
lemma num_W15 : ((G13 + 1) / 2 ^ 128) ^ 56 * ((F12 + 1) / 2 ^ 128)
      + (F13 + 1) / 2 ^ 128 * ((((G13 + 1) / 2 ^ 128) ^ 56 - 1) / ((G13 + 1) / 2 ^ 128 - 1))
    < 212366032807211 * (1 - (G12 + 1) / 2 ^ 128 * ((G13 + 1) / 2 ^ 128) ^ 56) := by
  norm_num

local notation "γh13" => ((G13 + 1) / 2 ^ 128 : ℚ)
local notation "γl13" => (G13 / 2 ^ 128 : ℚ)
local notation "γh12" => ((G12 + 1) / 2 ^ 128 : ℚ)
local notation "γl12" => (G12 / 2 ^ 128 : ℚ)

lemma num_W13 : (F13 + 1) / 2 ^ 128 < 212366032807211 * (1 - γh13) := by norm_num

lemma num_alpha : γh12 * γh13 ^ 56 * (1 + 115 / 10 ^ 10) ≤ 1 := by norm_num

lemma num_g15_lo : 1 / 3 < (γl12 * γl13 ^ 56) ^ 5 := by norm_num

lemma num_A2_lo : 1 / 3 < γl13 * (γl12 * γl13 ^ 56) ^ 5 := by norm_num

set_option exponentiation.threshold 400 in
lemma num_beta : 1 + 34 / 10 ^ 10 ≤ γl12 ^ 5 * γl13 ^ 279 := by norm_num

set_option exponentiation.threshold 400 in
lemma num_gN : 1 / 3 < γl12 ^ 6 * γl13 ^ 335 ∧ γh12 ^ 6 * γh13 ^ 335 < 1 := by norm_num

set_option exponentiation.threshold 400 in
lemma num_QN : 212366032807211 * (1 - γl12 ^ 6 * γl13 ^ 335)
    ≤ γl13 ^ 56 * (F12 / 2 ^ 128) + F13 / 2 ^ 128 * ((γl13 ^ 56 - 1) / (γl13 - 1)) := by norm_num

lemma num_small : 0 < γl12 ∧ 0 < γl13 ∧ γh13 < 1 ∧ γl13 < 1 ∧ γl12 ≤ 1 + 1 := by norm_num

/-! ## Generic arithmetic (abstract variables: no word and no huge power is ever unfolded) -/

lemma ar_up {g g' f f' c c' φ φ' B : ℚ} (k : ℕ) (hg0 : 0 ≤ g) (hg : g ≤ c) (hg' : g' ≤ c') (hf0 : 0 ≤ f)
    (hf : f ≤ φ) (hf' : f' ≤ φ') (hc0 : 0 ≤ c') (hφ'0 : 0 ≤ φ') (hc1 : c ≠ 1) (hB : 0 ≤ B)
    (hnum : c ^ k * φ + φ' * ((c ^ k - 1) / (c - 1)) < B * (1 - c' * c ^ k)) :
    g ^ k * f + f' * ∑ i ∈ Finset.range k, g ^ i < B * (1 - g' * g ^ k) := by
  have hS : ∑ i ∈ Finset.range k, g ^ i ≤ ∑ i ∈ Finset.range k, c ^ i :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hg0 hg i
  have hS0 : 0 ≤ ∑ i ∈ Finset.range k, g ^ i := Finset.sum_nonneg fun i _ => pow_nonneg hg0 i
  have hk : g ^ k ≤ c ^ k := pow_le_pow_left₀ hg0 hg k
  have t1 : g ^ k * f ≤ c ^ k * φ := mul_le_mul hk hf hf0 (pow_nonneg (hg0.trans hg) k)
  have t2 : f' * ∑ i ∈ Finset.range k, g ^ i ≤ φ' * ∑ i ∈ Finset.range k, c ^ i := mul_le_mul hf' hS hS0 hφ'0
  have t3 : g' * g ^ k ≤ c' * c ^ k := mul_le_mul hg' hk (pow_nonneg hg0 k) hc0
  have t4 := mul_le_mul_of_nonneg_left t3 hB
  rw [geom_sum_eq hc1] at t2
  linarith

lemma ar_low {g g' f f' c c' φ φ' B : ℚ} (k : ℕ) (hc0 : 0 ≤ c) (hg : c ≤ g) (hg' : c' ≤ g') (hφ0 : 0 ≤ φ)
    (hf : φ ≤ f) (hf' : φ' ≤ f') (hc0' : 0 ≤ c') (hφ'0 : 0 ≤ φ') (hc1 : c ≠ 1) (hB : 0 ≤ B) (r : ℕ)
    (hnum : B * (1 - c' ^ r * c ^ (r * 56 - 1)) ≤ c ^ k * φ + φ' * ((c ^ k - 1) / (c - 1))) :
    B * (1 - g' ^ r * g ^ (r * 56 - 1)) ≤ g ^ k * f + f' * ∑ i ∈ Finset.range k, g ^ i := by
  have hS : ∑ i ∈ Finset.range k, c ^ i ≤ ∑ i ∈ Finset.range k, g ^ i :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hc0 hg i
  have hS0 : 0 ≤ ∑ i ∈ Finset.range k, c ^ i := Finset.sum_nonneg fun i _ => pow_nonneg hc0 i
  have hk : c ^ k ≤ g ^ k := pow_le_pow_left₀ hc0 hg k
  have t1 : c ^ k * φ ≤ g ^ k * f := mul_le_mul hk hf hφ0 (pow_nonneg (hc0.trans hg) k)
  have t2 : φ' * ∑ i ∈ Finset.range k, c ^ i ≤ f' * ∑ i ∈ Finset.range k, g ^ i :=
    mul_le_mul hf' hS hS0 (hφ'0.trans hf')
  have t3 : c' ^ r * c ^ (r * 56 - 1) ≤ g' ^ r * g ^ (r * 56 - 1) :=
    mul_le_mul (pow_le_pow_left₀ hc0' hg' r) (pow_le_pow_left₀ hc0 hg _) (pow_nonneg hc0 _)
      (pow_nonneg (hc0'.trans hg') r)
  have t4 := mul_le_mul_of_nonneg_left t3 hB
  rw [geom_sum_eq hc1] at t2
  linarith

lemma ar_X {P Q c α : ℚ} (hP : 0 < P) (hQ : 0 < Q) (h : Q / P ≤ c) (hα : c * (1 + α) ≤ 1) (hα0 : 0 ≤ 1 + α) :
    1 + α ≤ P / Q := by
  rw [le_div_iff₀ hQ]
  rw [div_le_iff₀ hP] at h
  calc (1 + α) * Q ≤ (1 + α) * (c * P) := mul_le_mul_of_nonneg_left h hα0
    _ = (c * (1 + α)) * P := by ring
    _ ≤ 1 * P := mul_le_mul_of_nonneg_right hα hP.le
    _ = P := one_mul P

lemma ar_div {B P T φ : ℚ} (hP : 0 < P) (h : B * (1 - T / P) ≤ φ / P) : B * (P - T) ≤ φ := by
  rw [show B * (1 - T / P) = B * (P - T) / P by field_simp] at h
  rwa [div_le_div_iff_of_pos_right hP] at h

lemma mul_pow_le {a b x y : ℚ} {r s : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : a ≤ x) (hy : b ≤ y) :
    a ^ r * b ^ s ≤ x ^ r * y ^ s :=
  mul_le_mul (pow_le_pow_left₀ ha hx r) (pow_le_pow_left₀ hb hy s) (pow_nonneg hb s) (pow_nonneg (ha.trans hx) r)

/-! ## The words `W₁₄, W₁₅, W₁₆`, the exceptional words, the word of `p₁₈` -/

local notation "W12" => stilde 176251 111202
local notation "W13" => stilde 301994 190537
local notation "W14" => stilde 16785921 10590737
local notation "W15" => stilde 17087915 10781274
local notation "W16" => stilde 85137581 53715833

lemma W14_eq : W14 = W12 ++ wpow W13 55 := by
  have := stilde_append_wpow (lu := 176251) (nu := 111202) (lv := 301994) (nv := 190537)
    (by norm_num) (by norm_num) (by norm_num) 55
  rwa [show (176251 + 55 * 301994 : ℕ) = 16785921 by norm_num,
    show (111202 + 55 * 190537 : ℕ) = 10590737 by norm_num] at this

lemma W15_eq : W15 = W12 ++ wpow W13 56 := by
  have := stilde_append_wpow (lu := 176251) (nu := 111202) (lv := 301994) (nv := 190537)
    (by norm_num) (by norm_num) (by norm_num) 56
  rwa [show (176251 + 56 * 301994 : ℕ) = 17087915 by norm_num,
    show (111202 + 56 * 190537 : ℕ) = 10781274 by norm_num] at this

lemma W16_eq : W16 = W14 ++ wpow W15 4 := by
  have := stilde_append_wpow (lu := 16785921) (nu := 10590737) (lv := 17087915) (nv := 10781274)
    (by norm_num) (by norm_num) (by norm_num) 4
  rwa [show (16785921 + 4 * 17087915 : ℕ) = 85137581 by norm_num,
    show (10590737 + 4 * 10781274 : ℕ) = 53715833 by norm_num] at this

lemma WN_eq : stilde 102225496 64497107 = W16 ++ W15 := by
  have := stilde_append_thm 85137581 53715833 17087915 10781274 (by norm_num) (by norm_num) (by norm_num)
  rwa [show (85137581 + 17087915 : ℕ) = 102225496 by norm_num,
    show (53715833 + 10781274 : ℕ) = 64497107 by norm_num] at this

lemma WA2_eq (k : ℕ) : stilde (k * 17087915 + 301994) (k * 10781274 + 190537) = wpow W15 k ++ W13 :=
  stilde_wpow_append (lu := 301994) (nu := 190537) (lv := 17087915) (nv := 10781274)
    (by norm_num) (by norm_num) (by norm_num) k

lemma WA1_eq (a : ℕ) : stilde (a * 17087915) (a * 10781274) = wpow W15 a :=
  stilde_wpow_thm a _ _ (by norm_num)

/-! ## `f` and `g` of `W₁₅`, `W₁₆`, `W₁₈` -/

lemma gw_W15 : gw W15 = gw W12 * gw W13 ^ 56 := by rw [W15_eq, gw_append, gw_wpow]

lemma fw_W15 : fw W15 = gw W13 ^ 56 * fw W12 + fw W13 * ∑ i ∈ Finset.range 56, gw W13 ^ i := by
  rw [W15_eq, fw_append, gw_wpow, fw_wpow]

lemma gw_W16 : gw W16 = gw W12 ^ 5 * gw W13 ^ 279 := by
  rw [W16_eq, gw_append, gw_wpow, W14_eq, gw_append, gw_wpow, gw_W15]; ring

lemma gw_WN : gw (stilde 102225496 64497107) = gw W12 ^ 6 * gw W13 ^ 335 := by
  rw [WN_eq, gw_append, gw_W16, gw_W15]; ring

lemma g15_bounds : (γl12 * γl13 ^ 56) ≤ gw W15 ∧ gw W15 ≤ γh12 * γh13 ^ 56 := by
  obtain ⟨a1, a2⟩ := g12_encl
  obtain ⟨b1, b2⟩ := g13_encl
  rw [gw_W15]
  have h1 := mul_pow_le (r := 1) (s := 56) (by norm_num) (by norm_num) a1 b1
  have h2 := mul_pow_le (r := 1) (s := 56) (gw_pos W12).le (gw_pos W13).le a2.le b2.le
  simp only [pow_one] at h1 h2
  exact ⟨h1, h2⟩

/-- The Third step: `ϕ(W₁₆) < m (2^{p₁₆} − 3^{q₁₆})` (paper's index; Mathlib's `W₁₅`). -/
lemma good_W15 : good 212366032807211 W15 := by
  rw [good_iff, fw_W15, gw_W15]
  exact ar_up 56 (gw_pos W13).le g13_encl.2.le g12_encl.2.le (fw_nonneg W12) f12_encl.2.le f13_encl.2.le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) num_W15

lemma good_W13 : good 212366032807211 W13 := by
  rw [good_iff]
  obtain ⟨b1, b2⟩ := g13_encl
  obtain ⟨d1, d2⟩ := f13_encl
  have := num_W13
  linarith

/-- `n(l) = n` from `1/3 < g(s̃(l,n)) < 1`. -/
lemma nOf_of_gw {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (h1 : gw (stilde l n) < 1) (h2 : 1 / 3 < gw (stilde l n)) :
    nOf l = n := by
  rw [gw_stilde hl hn] at h1 h2
  have hp : (0 : ℚ) < 2 ^ l := by positivity
  apply nOf_of_q hl
  · rwa [div_lt_one hp] at h1
  · rw [lt_div_iff₀ hp] at h2
    rw [pow_succ]
    linarith

lemma g15_lt_one : gw W15 < 1 := by
  have h1 := g15_bounds.2
  have h2 := num_alpha
  have h3 : 0 < γh12 * γh13 ^ 56 := by norm_num
  have h4 : γh12 * γh13 ^ 56 < 1 := by nlinarith
  exact lt_of_le_of_lt h1 h4

lemma g15_pow_lo {a : ℕ} (ha5 : a ≤ 5) : (γl12 * γl13 ^ 56) ^ 5 ≤ gw W15 ^ a :=
  le_trans (pow_le_pow_left₀ (by norm_num) g15_bounds.1 5)
    (pow_le_pow_of_le_one (gw_pos W15).le g15_lt_one.le ha5)

lemma nOf_A1 (a : ℕ) (ha : 1 ≤ a) (ha5 : a ≤ 5) : nOf (a * 17087915) = a * 10781274 := by
  apply nOf_of_gw (by omega) (by omega)
  · rw [WA1_eq, gw_wpow]; exact pow_lt_one₀ (gw_pos W15).le g15_lt_one (by omega)
  · rw [WA1_eq, gw_wpow]; exact lt_of_lt_of_le num_g15_lo (g15_pow_lo ha5)

lemma nOf_A2 (k : ℕ) (hk5 : k ≤ 5) : nOf (k * 17087915 + 301994) = k * 10781274 + 190537 := by
  apply nOf_of_gw (by omega) (by omega)
  · rw [WA2_eq, gw_append, gw_wpow]
    have h1 : gw W15 ^ k ≤ 1 := pow_le_one₀ (gw_pos W15).le g15_lt_one.le
    have h2 : gw W13 < 1 := lt_trans g13_encl.2 (by norm_num)
    have h3 := gw_pos W13
    have h4 : 0 ≤ gw W15 ^ k := pow_nonneg (gw_pos W15).le k
    nlinarith
  · rw [WA2_eq, gw_append, gw_wpow, mul_comm]
    exact lt_of_lt_of_le num_A2_lo
      (mul_le_mul g13_encl.1 (g15_pow_lo hk5) (by norm_num) (gw_pos W13).le)

lemma nOf_p16 : nOf 17087915 = 10781274 := by simpa using nOf_A1 1 le_rfl (by norm_num)

/-- `1 + α ≤ X = 2^{p₁₆}/3^{q₁₆}` (paper's index). -/
lemma X_ge : 1 + 115 / 10 ^ 10 ≤ (2 : ℚ) ^ 17087915 / 3 ^ 10781274 := by
  have h := g15_bounds.2
  rw [gw_stilde (by norm_num) (by norm_num)] at h
  exact ar_X (by positivity) (by positivity) h num_alpha (by norm_num)

/-- `1 + β ≤ Y = 3^{q₁₇}/2^{p₁₇}` (paper's index). -/
lemma Y_ge : 1 + 34 / 10 ^ 10 ≤ (3 : ℚ) ^ 53715833 / 2 ^ 85137581 := by
  rw [← gw_stilde (l := 85137581) (n := 53715833) (by norm_num) (by norm_num), gw_W16]
  exact le_trans num_beta (mul_pow_le (by norm_num) (by norm_num) g12_encl.1 g13_encl.1)

lemma nOf_pN : nOf 102225496 = 64497107 := by
  apply nOf_of_gw (by norm_num) (by norm_num)
  · rw [gw_WN]
    exact lt_of_le_of_lt (mul_pow_le (gw_pos W12).le (gw_pos W13).le g12_encl.2.le g13_encl.2.le) num_gN.2
  · rw [gw_WN]
    exact lt_of_lt_of_le num_gN.1 (mul_pow_le (by norm_num) (by norm_num) g12_encl.1 g13_encl.1)

/-- `p₁₈ = 102 225 496`: `m ≤ Q4(p₁₈)` (optimality of the example). -/
lemma Q4_pN : 212366032807211 ≤ Q4 102225496 := by
  apply le_Q4_of (by norm_num) nOf_pN
  have key : 212366032807211 * (1 - gw (stilde 102225496 64497107)) ≤ fw (stilde 102225496 64497107) := by
    have hlow : 212366032807211 * (1 - gw W12 ^ 6 * gw W13 ^ (6 * 56 - 1))
        ≤ gw W13 ^ 56 * fw W12 + fw W13 * ∑ i ∈ Finset.range 56, gw W13 ^ i :=
      ar_low 56 (by norm_num) g13_encl.1 g12_encl.1 (by norm_num) f12_encl.1 f13_encl.1 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) 6 num_QN
    rw [gw_WN]
    rw [show 6 * 56 - 1 = 335 by norm_num] at hlow
    rw [← fw_W15] at hlow
    have h2 : fw W15 ≤ fw (stilde 102225496 64497107) := by
      rw [WN_eq, fw_append]
      have := fw_nonneg W16
      have := gw_pos W15
      nlinarith
    exact le_trans hlow h2
  unfold fw gw at key
  rw [stilde_length, stilde_count (by norm_num) (by norm_num)] at key
  exact ar_div (by positivity) key

end LaboHH
