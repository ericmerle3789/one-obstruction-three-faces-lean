import Mathlib
import Lagarias.L1990b_Enonces
import Lagarias.L4_Preuves

/-!
# Lagarias 1990 · Theorem 4.2 · proofs (phase 2b)

Ash's tail bound is proved here (Chernoff's argument). The proof of Theorem 4.2 follows the paper with one
simplification of the exceptional set (each oversize window bounds ONE term of `N(v)`, instead of summing the
windows as in (4.10)), and with the exact identity `H + (2 − H)·α_c = 1`, so no numerical value of `α_c` is used.
The constant is the one the printed proof gives, `4n⁴` (the statement prints `2n⁴`).
Statements: `Lagarias/L1990b_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP LaboHH

/-! ## Ash's tail bound -/

lemma Hb_eq (a : ℝ) : Hb a * Real.log 2 = -a * Real.log a - (1 - a) * Real.log (1 - a) := by
  unfold Hb Real.logb
  have : Real.log 2 ≠ 0 := by positivity
  field_simp

theorem ash_tail_thm : ash_tail := by
  intro k a ha1 ha2
  rcases ha2.lt_or_eq with ha2 | rfl
  · -- `1/2 ≤ a < 1`: Chernoff with `t = a/(1−a) ≥ 1`
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < 1 - a := by linarith
    set t := a / (1 - a) with ht
    have ht0 : 0 < t := div_pos ha0 hb0
    have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hb0]; linarith
    calc ∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => a * (k : ℝ) ≤ (j : ℝ)), (k.choose j : ℝ)
        ≤ ∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => a * (k : ℝ) ≤ (j : ℝ)),
            (k.choose j : ℝ) * t ^ ((j : ℝ) - a * k) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_filter] at hj
          have : 1 ≤ t ^ ((j : ℝ) - a * k) := Real.one_le_rpow ht1 (by linarith [hj.2])
          have hc : (0 : ℝ) ≤ k.choose j := by positivity
          nlinarith
      _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * t ^ ((j : ℝ) - a * k) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro j _ _; positivity
      _ = t ^ (-(a * k)) * (1 + t) ^ k := by
          rw [add_comm 1 t, add_pow, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_natCast]
          simp only [one_pow, mul_one]; ring
      _ = 2 ^ (Hb a * k) := by
          rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
            ← Real.exp_log (pow_pos (by linarith : (0 : ℝ) < 1 + t) k), ← Real.exp_add]
          congr 1
          rw [Real.log_pow, show 1 + t = 1 / (1 - a) by rw [ht]; field_simp; ring, ht,
            Real.log_div ha0.ne' hb0.ne', Real.log_div one_ne_zero hb0.ne', Real.log_one]
          have h := Hb_eq a
          linear_combination (-(k : ℝ)) * h
  · -- `a = 1`
    have hfilter : (Finset.range (k + 1)).filter (fun j : ℕ => 1 * (k : ℝ) ≤ (j : ℝ)) = {k} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, one_mul]
      constructor
      · rintro ⟨h1, h2⟩; have : k ≤ j := by exact_mod_cast h2
        omega
      · rintro rfl; exact ⟨by omega, le_rfl⟩
    rw [hfilter]
    simp [Hb]

/-! ## Words counted by weight -/

lemma card_words_count (k i : ℕ) : ((words k).filter (fun u => u.count true = i)).card = k.choose i := by
  induction k generalizing i with
  | zero =>
    rcases i with _ | i
    · rfl
    · simp [words]
  | succ k ih =>
    have hsplit : (words (k + 1)).filter (fun u => u.count true = i) =
        ((words k).filter (fun w => (true :: w).count true = i)).image (List.cons true) ∪
          ((words k).filter (fun w => (false :: w).count true = i)).image (List.cons false) := by
      simp only [words, Finset.filter_union, Finset.filter_image]
    rw [hsplit, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective]
    · have h2 : (words k).filter (fun w => (false :: w).count true = i) =
          (words k).filter (fun w => w.count true = i) :=
        Finset.filter_congr (fun w _ => by simp)
      rw [h2, ih]
      rcases i with _ | i
      · have : (words k).filter (fun w => (true :: w).count true = 0) = ∅ := by
          ext w; simp
        rw [this]; simp
      · have h1 : (words k).filter (fun w => (true :: w).count true = i + 1) =
            (words k).filter (fun w => w.count true = i) :=
          Finset.filter_congr (fun w _ => by simp)
        rw [h1, ih, Nat.choose_succ_succ, add_comm]
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_image] at h1 h2
      obtain ⟨_, _, rfl⟩ := h1
      obtain ⟨_, _, h⟩ := h2
      simp at h

lemma count_le_of_mem_words {k : ℕ} {u : List Bool} (hu : u ∈ words k) : u.count true ≤ k := by
  rw [mem_words] at hu
  rw [← hu]; exact List.count_le_length

/-- Ash's bound on words. -/
lemma words_tail (k : ℕ) (a : ℝ) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 1) :
    (((words k).filter (fun u => a * (k : ℝ) ≤ (u.count true : ℝ))).card : ℝ) ≤ 2 ^ (Hb a * k) := by
  refine le_trans ?_ (ash_tail_thm k a ha1 ha2)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun u => u.count true)
    (t := (Finset.range (k + 1)).filter (fun j : ℕ => a * (k : ℝ) ≤ (j : ℝ)))]
  · push_cast
    apply le_of_eq
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_filter] at hj
    rw [Finset.filter_filter, ← card_words_count k j]
    congr 2
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h0, -, h⟩; exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩; exact ⟨h0, by rw [h]; exact hj.2, h⟩
  · intro u hu
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hu ⊢
    exact ⟨Nat.lt_succ_of_le (count_le_of_mem_words hu.1), hu.2⟩

/-! ## Windows -/

lemma window_split (v : List Bool) (l m : ℕ) :
    v = v.take l ++ (v.drop l).take m ++ v.drop (l + m) := by
  conv_lhs => rw [← List.take_append_drop l v, ← List.take_append_drop m (v.drop l)]
  rw [List.drop_drop, List.append_assoc]

/-- (4.9): `N(v) ≥ 2^l 3^{B} N(window)`. -/
lemma C_ge_window (v : List Bool) (l m : ℕ) (hl : l ≤ v.length) :
    2 ^ l * 3 ^ (v.drop (l + m)).count true * C ((v.drop l).take m) ≤ C v := by
  have e := eq4_8_thm (v.take l) ((v.drop l).take m) (v.drop (l + m))
  rw [← window_split, List.length_take, Nat.min_eq_left hl] at e
  rw [e]
  omega

lemma count_drop_succ_le (v : List Bool) (i : ℕ) :
    (v.drop (i + 1)).count true ≤ (v.drop i).count true := by
  rw [show i + 1 = i + 1 by rfl, ← List.drop_drop]
  exact (List.drop_sublist 1 _).count_le _

/-- The summand of `N(v) = Σ_i v_i 2^i 3^{v_{i+1}+…}` (`LaboBP.Csum`). -/
def term (v : List Bool) (i : ℕ) : ℕ :=
  if v.getD i false then 2 ^ i * 3 ^ ((v.drop (i + 1)).count true) else 0

lemma C_eq_sum_term (v : List Bool) : C v = ∑ i ∈ Finset.range v.length, term v i := by
  rw [C_eq_Csum v]; rfl

lemma term_le (v : List Bool) (i : ℕ) : term v i ≤ 2 ^ i * 3 ^ (v.drop i).count true := by
  unfold term
  split_ifs
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (count_drop_succ_le v i))
  · exact Nat.zero_le _

/-- The exceptional vectors (p. 49, simplified): if every window of length `m` is oversize, some position
`j < m` carries a term `≥ 2ⁿ`. -/
lemma exceptional (n m M : ℕ) (v : List Bool) (hv : v.length = n) (hn : 0 < n) (hmn : m ≤ n)
    (hM : 2 * n ^ 2 * 2 ^ m ≤ M) (hall : ∀ l, l + m ≤ n → M ≤ C ((v.drop l).take m)) :
    ∃ j < m, v.getD j false = true ∧ 2 ^ n ≤ 2 ^ j * 3 ^ (v.drop (j + 1)).count true := by
  set N := C v with hN
  -- each high term is small
  have hhigh : ∀ i, m ≤ i → i < n → 2 * n ^ 2 * (2 ^ i * 3 ^ (v.drop i).count true) ≤ N := by
    intro i hmi hin
    have h1 := C_ge_window v (i - m) m (by omega)
    rw [show i - m + m = i by omega] at h1
    have h2 := hall (i - m) (by omega)
    have h3 : 2 ^ i = 2 ^ (i - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
    calc 2 * n ^ 2 * (2 ^ i * 3 ^ (v.drop i).count true)
        = 2 ^ (i - m) * 3 ^ (v.drop i).count true * (2 * n ^ 2 * 2 ^ m) := by rw [h3]; ring
      _ ≤ 2 ^ (i - m) * 3 ^ (v.drop i).count true * C ((v.drop (i - m)).take m) :=
          Nat.mul_le_mul_left _ (hM.trans h2)
      _ ≤ N := h1
  -- the last window
  have hlast : 2 * n ^ 2 * 2 ^ n ≤ N := by
    have h1 := C_ge_window v (n - m) m (by omega)
    rw [show n - m + m = n by omega, ← hv, List.drop_length, hv] at h1
    have h2 := hall (n - m) (by omega)
    have h3 : 2 ^ n = 2 ^ (n - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
    calc 2 * n ^ 2 * 2 ^ n = 2 ^ (n - m) * (2 * n ^ 2 * 2 ^ m) := by rw [h3]; ring
      _ ≤ 2 ^ (n - m) * C ((v.drop (n - m)).take m) := Nat.mul_le_mul_left _ (hM.trans h2)
      _ ≤ N := by simpa using h1
  -- split the sum
  have hsplit : N = ∑ i ∈ Finset.range m, term v i + ∑ i ∈ Finset.Ico m n, term v i := by
    rw [hN, C_eq_sum_term, hv, Finset.sum_range_add_sum_Ico _ hmn]
  have hhi : 2 * n ^ 2 * ∑ i ∈ Finset.Ico m n, term v i ≤ n * N := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.Ico m n, 2 * n ^ 2 * term v i
        ≤ ∑ i ∈ Finset.Ico m n, N := Finset.sum_le_sum fun i hi => by
          rw [Finset.mem_Ico] at hi
          exact (Nat.mul_le_mul_left _ (term_le v i)).trans (hhigh i hi.1 hi.2)
      _ = (n - m) * N := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      _ ≤ n * N := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hlo : n ^ 2 * 2 ^ n ≤ ∑ i ∈ Finset.range m, term v i := by
    have h2 : 2 * n * ∑ i ∈ Finset.Ico m n, term v i ≤ N := by
      have : n * (2 * n * ∑ i ∈ Finset.Ico m n, term v i) ≤ n * N := by
        calc n * (2 * n * ∑ i ∈ Finset.Ico m n, term v i) = 2 * n ^ 2 * ∑ i ∈ Finset.Ico m n, term v i := by ring
          _ ≤ n * N := hhi
      exact Nat.le_of_mul_le_mul_left this hn
    have h3 : 2 * ∑ i ∈ Finset.Ico m n, term v i ≤ N := by
      calc 2 * ∑ i ∈ Finset.Ico m n, term v i ≤ 2 * n * ∑ i ∈ Finset.Ico m n, term v i := by
            apply Nat.mul_le_mul_right; omega
        _ ≤ N := h2
    have e : 2 * n ^ 2 * 2 ^ n = 2 * (n ^ 2 * 2 ^ n) := by ring
    omega
  have hm0 : 0 < m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, Finset.range_zero, Finset.sum_empty] at hlo
    have : 0 < n ^ 2 * 2 ^ n := by positivity
    omega
  obtain ⟨j, hj, hjt⟩ : ∃ j ∈ Finset.range m, 2 ^ n ≤ term v j := by
    apply Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr hm0.ne')
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    calc m * 2 ^ n ≤ n ^ 2 * 2 ^ n := Nat.mul_le_mul_right _ (by nlinarith)
      _ ≤ _ := hlo
  rw [Finset.mem_range] at hj
  unfold term at hjt
  split_ifs at hjt with hb
  · exact ⟨j, hj, hb, hjt⟩
  · have : 0 < 2 ^ n := by positivity
    omega

/-- Normal windows (p. 48): at a fixed position, at most `(m+1)·2^{n−m}` vectors of a class mod `M`. -/
lemma normal_count (n M m l r : ℕ) (hM : 0 < M) (hcop : Nat.Coprime M 6) (hlm : l + m ≤ n) :
    ((words n).filter (fun v => C v % M = r % M ∧ C ((v.drop l).take m) < M)).card ≤
      (m + 1) * 2 ^ (n - m) := by
  have hcard : ((words l ×ˢ words (n - (l + m))) ×ˢ Finset.range (m + 1)).card = (m + 1) * 2 ^ (n - m) := by
    rw [Finset.card_product, Finset.card_product, card_words, card_words, Finset.card_range, ← pow_add,
      show l + (n - (l + m)) = n - m by omega]
    ring
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun v => ((v.take l, v.drop (l + m)), ((v.drop l).take m).count true))
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_words] at hv
    obtain ⟨hvl, -, -⟩ := hv
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_words, Finset.mem_range]
    refine ⟨⟨by simp [hvl]; omega, by simp [hvl]⟩, Nat.lt_succ_of_le ?_⟩
    exact (List.count_le_length).trans (by simp)
  · intro v1 hv1 v2 hv2 h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_words] at hv1 hv2
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨hw, hw'⟩, hc⟩ := h
    have hl1 : (v1.take l).length = l := by simp [hv1.1]; omega
    have hu1 : ((v1.drop l).take m).length = m := by simp [hv1.1]; omega
    have hu2 : ((v2.drop l).take m).length = m := by simp [hv2.1]; omega
    have e1 := eq4_8_thm (v1.take l) ((v1.drop l).take m) (v1.drop (l + m))
    have e2 := eq4_8_thm (v2.take l) ((v2.drop l).take m) (v2.drop (l + m))
    rw [← window_split, hl1, hu1] at e1
    rw [← window_split, hu2, ← hw, ← hw', ← hc, hl1] at e2
    have hmod : 2 ^ l * 3 ^ (v1.drop (l + m)).count true * C ((v1.drop l).take m) ≡
        2 ^ l * 3 ^ (v1.drop (l + m)).count true * C ((v2.drop l).take m) [MOD M] := by
      have h12 : C v1 ≡ C v2 [MOD M] := by unfold Nat.ModEq; rw [hv1.2.1, hv2.2.1]
      rw [e1, e2] at h12
      have := Nat.ModEq.add_right_cancel' _ h12
      exact Nat.ModEq.add_left_cancel' _ this
    have hcop' : M.gcd (2 ^ l * 3 ^ (v1.drop (l + m)).count true) = 1 := by
      have c2 : Nat.Coprime M 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
      have c3 : Nat.Coprime M 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
      exact Nat.Coprime.mul_right (c2.pow_right _) (c3.pow_right _)
    have hCeq := (Nat.ModEq.cancel_left_of_coprime hcop' hmod).eq_of_lt_of_lt hv1.2.2 hv2.2.2
    have hu := cor2_1a_words_thm _ _ (by rw [hu1, hu2]) hc hCeq
    rw [window_split v1 l m, window_split v2 l m, hw, hu, hw']

/-! ## Constants -/

lemma phiL_bounds : 1 / 2 ≤ phiL ∧ phiL ≤ 1 := by
  unfold phiL Real.logb
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h34 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  constructor
  · rw [le_div_iff₀ h3]; linarith
  · rw [div_le_one h3]; exact h23

lemma Hb_bounds (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ Hb x ∧ Hb x ≤ 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : Hb x * Real.log 2 = Real.binEntropy x := by
    rw [Hb_eq, Real.binEntropy, Real.log_inv, Real.log_inv]; ring
  have hb0 := Real.binEntropy_nonneg h0 h1
  have hb1 := Real.binEntropy_le_log_two (p := x)
  constructor
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith

lemma exc_card (n j : ℕ) (hj : j < n) (a : ℝ) :
    ((words n).filter (fun v => a * ((n - j - 1 : ℕ) : ℝ) ≤ ((v.drop (j + 1)).count true : ℝ))).card ≤
      2 ^ (j + 1) * ((words (n - j - 1)).filter (fun u => a * ((n - j - 1 : ℕ) : ℝ) ≤ (u.count true : ℝ))).card := by
  rw [← card_words (j + 1), ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun v => (v.take (j + 1), v.drop (j + 1)))
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_words] at hv
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_words, Finset.mem_filter,
      List.length_take, List.length_drop, hv.1]
    refine ⟨by omega, by omega, hv.2⟩
  · intro v1 _ v2 _ h
    simp only [Prod.mk.injEq] at h
    rw [← List.take_append_drop (j + 1) v1, ← List.take_append_drop (j + 1) v2, h.1, h.2]

lemma count_of_term (n j c : ℕ) (hj : j < n) (h : 2 ^ n ≤ 2 ^ j * 3 ^ c) :
    phiL * ((n - j - 1 : ℕ) : ℝ) ≤ (c : ℝ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpow : 2 ^ (n - j) ≤ 3 ^ c := by
    have : 2 ^ n = 2 ^ j * 2 ^ (n - j) := by rw [← pow_add]; congr 1; omega
    rw [this] at h
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  have hlog : ((n - j : ℕ) : ℝ) * Real.log 2 ≤ (c : ℝ) * Real.log 3 := by
    rw [← Real.log_pow, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have hφ : phiL * ((n - j : ℕ) : ℝ) ≤ c := by
    unfold phiL Real.logb
    rw [div_mul_eq_mul_div, div_le_iff₀ h3]; linarith
  have hφ0 : 0 ≤ phiL := by linarith [phiL_bounds.1]
  have hmono : ((n - j - 1 : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) := by exact_mod_cast (by omega : n - j - 1 ≤ n - j)
  nlinarith

/-! ## Theorem 4.2 -/

theorem thm4_2_thm : thm4_2 := by
  intro n M hn hM hcop hMα r
  obtain ⟨hφ1, hφ2⟩ := phiL_bounds
  obtain ⟨hH0, hH1⟩ := Hb_bounds phiL (by linarith) hφ2
  set H := Hb phiL with hH
  have h2H : 0 < 2 - H := by linarith
  have hαc : (2 - H) * alphaC = 1 - H := by unfold alphaC; rw [← hH]; field_simp
  have hαc1 : alphaC ≤ 1 := by
    have : (2 - H) * alphaC ≤ (2 - H) * 1 := by rw [hαc]; linarith
    exact le_of_mul_le_mul_left this h2H
  have hcnt : cntRes n M r ≤ 2 ^ n := (Finset.card_filter_le _ _).trans (card_words n).le
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hA : (M : ℝ) ≤ 4 * n ^ 4
  · have : (cntRes n M r : ℝ) ≤ 2 ^ n := by exact_mod_cast hcnt
    calc (cntRes n M r : ℝ) * M ≤ 2 ^ n * (4 * n ^ 4) :=
          mul_le_mul this hA (by positivity) (by positivity)
      _ = 4 * n ^ 4 * 2 ^ n := by ring
  push Not at hA
  -- `M ≤ 2ⁿ`, hence `n ≥ 4`
  have hMn : (M : ℝ) ≤ 2 ^ n := by
    calc (M : ℝ) ≤ 2 ^ (alphaC * n) := hMα
      _ ≤ 2 ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = 2 ^ n := Real.rpow_natCast 2 n
  have hn4 : 4 ≤ n := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ^ n ≤ 4 * n ^ 4 := by
      interval_cases n <;> norm_num
    linarith
  -- the window length `m`: `2n²·2^m ≤ M < 4n²·2^m`
  have hnn : 0 < 2 * n ^ 2 := by positivity
  set q := M / (2 * n ^ 2) with hq
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn24 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by nlinarith
  have hMq : 2 * n ^ 2 ≤ M := by
    have : ((2 * n ^ 2 : ℕ) : ℝ) ≤ M := by push_cast; linarith
    exact_mod_cast this
  have hq0 : q ≠ 0 := by rw [hq]; exact (Nat.div_pos hMq hnn).ne'
  set m := Nat.log 2 q with hm
  have hm1 : 2 ^ m ≤ q := Nat.pow_log_le_self 2 hq0
  have hm2 : q < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have hMlow : 2 * n ^ 2 * 2 ^ m ≤ M := (Nat.mul_le_mul_left _ hm1).trans (Nat.mul_div_le M _)
  have hMup : M < 4 * n ^ 2 * 2 ^ m := by
    have h1 : M < 2 * n ^ 2 * (q + 1) := Nat.lt_mul_div_succ M hnn
    have h2 : q + 1 ≤ 2 ^ (m + 1) := hm2
    calc M < 2 * n ^ 2 * (q + 1) := h1
      _ ≤ 2 * n ^ 2 * 2 ^ (m + 1) := Nat.mul_le_mul_left _ h2
      _ = 4 * n ^ 2 * 2 ^ m := by ring
  have hmn : m < n := by
    have h1 : 2 ^ m < 2 ^ n := by
      have : (M : ℝ) ≤ 2 ^ n := hMn
      have h2 : ((2 * n ^ 2 * 2 ^ m : ℕ) : ℝ) ≤ M := by exact_mod_cast hMlow
      push_cast at h2
      have hp : (0 : ℝ) < 2 ^ m := by positivity
      have h3 : (2 : ℝ) * 2 ^ m ≤ 2 * n ^ 2 * 2 ^ m := by nlinarith
      have : (2 : ℝ) ^ m < 2 ^ n := by linarith
      exact_mod_cast this
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have hmα : (m : ℝ) ≤ alphaC * n := by
    have h1 : (2 : ℝ) ^ (m : ℝ) ≤ 2 ^ (alphaC * n) := by
      rw [Real.rpow_natCast]
      have : ((2 ^ m : ℕ) : ℝ) ≤ M := by exact_mod_cast (hm1.trans (Nat.div_le_self _ _))
      push_cast at this
      linarith
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).mp h1
  -- covering of the class
  set S := (words n).filter (fun v => C v % M = r % M) with hS
  set Nor := fun l => (words n).filter (fun v => C v % M = r % M ∧ C ((v.drop l).take m) < M)
  set Exc := fun j => (words n).filter
    (fun v => phiL * ((n - j - 1 : ℕ) : ℝ) ≤ ((v.drop (j + 1)).count true : ℝ))
  have hcover : S ⊆ (Finset.range (n - m + 1)).biUnion Nor ∪ (Finset.range m).biUnion Exc := by
    intro v hv
    rw [hS, Finset.mem_filter, mem_words] at hv
    by_cases h : ∃ l, l + m ≤ n ∧ C ((v.drop l).take m) < M
    · obtain ⟨l, hl, hlt⟩ := h
      apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      exact ⟨l, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨(mem_words _ _).mpr hv.1, hv.2, hlt⟩⟩
    · push Not at h
      obtain ⟨j, hj, -, hjt⟩ := exceptional n m M v hv.1 hn hmn.le hMlow h
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨j, Finset.mem_range.mpr hj,
        Finset.mem_filter.mpr ⟨(mem_words _ _).mpr hv.1, count_of_term n j _ (by omega) hjt⟩⟩
  have hcard : cntRes n M r ≤ (n - m + 1) * ((m + 1) * 2 ^ (n - m)) +
      ∑ j ∈ Finset.range m, 2 ^ (j + 1) *
        ((words (n - j - 1)).filter (fun u => phiL * ((n - j - 1 : ℕ) : ℝ) ≤ (u.count true : ℝ))).card := by
    calc cntRes n M r = S.card := rfl
      _ ≤ ((Finset.range (n - m + 1)).biUnion Nor ∪ (Finset.range m).biUnion Exc).card :=
          Finset.card_le_card hcover
      _ ≤ ((Finset.range (n - m + 1)).biUnion Nor).card + ((Finset.range m).biUnion Exc).card :=
          Finset.card_union_le _ _
      _ ≤ ∑ l ∈ Finset.range (n - m + 1), (Nor l).card + ∑ j ∈ Finset.range m, (Exc j).card :=
          add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ ≤ _ := by
          apply add_le_add
          · calc ∑ l ∈ Finset.range (n - m + 1), (Nor l).card
                ≤ ∑ l ∈ Finset.range (n - m + 1), (m + 1) * 2 ^ (n - m) :=
                  Finset.sum_le_sum fun l hl => normal_count n M m l r hM hcop
                    (by rw [Finset.mem_range] at hl; omega)
              _ = (n - m + 1) * ((m + 1) * 2 ^ (n - m)) := by
                  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          · exact Finset.sum_le_sum fun j hj => exc_card n j (by rw [Finset.mem_range] at hj; omega) phiL
  -- real estimates
  have hcardR : (cntRes n M r : ℝ) ≤ ((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) +
      ∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ)) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at h
    refine h.trans (add_le_add (le_of_eq (by push_cast; ring)) (Finset.sum_le_sum fun j _ => ?_))
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact words_tail (n - j - 1) phiL hφ1 hφ2
  have hMR : (M : ℝ) < 4 * n ^ 2 * 2 ^ m := by exact_mod_cast hMup
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  -- normal part
  have hnorm : ((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) * M ≤
      4 * n ^ 3 * (n - 1) * 2 ^ n := by
    have hprod : ((n - m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ≤ n * (n - 1) := by
      have e1 : ((n - m + 1 : ℕ) : ℝ) = n - m + 1 := by push_cast [Nat.cast_sub hmn.le]; ring
      rw [e1]; push_cast
      have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      nlinarith [sq_nonneg ((n : ℝ) - 2 * m)]
    have h2 : (2 : ℝ) ^ (n - m) * 2 ^ m = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hmn.le]
    calc ((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) * M
        = (((n - m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) * 2 ^ (n - m) * M := by ring
      _ ≤ (n * (n - 1)) * 2 ^ (n - m) * (4 * n ^ 2 * 2 ^ m) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hprod (by positivity)) hMR.le hMpos.le
          have : (0 : ℝ) ≤ n * (n - 1) := by nlinarith
          positivity
      _ = 4 * n ^ 3 * (n - 1) * (2 ^ (n - m) * 2 ^ m) := by ring
      _ = 4 * n ^ 3 * (n - 1) * 2 ^ n := by rw [h2]
  -- exceptional part
  have hexc : (∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ))) * M ≤
      n * 2 ^ n := by
    rw [Finset.sum_mul]
    calc ∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ)) * M
        ≤ ∑ j ∈ Finset.range m, (2 : ℝ) ^ n := Finset.sum_le_sum fun j hj => by
          rw [Finset.mem_range] at hj
          have e1 : ((n - j - 1 : ℕ) : ℝ) = n - j - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
          have hexp : ((j + 1 : ℕ) : ℝ) + H * ((n - j - 1 : ℕ) : ℝ) + alphaC * n ≤ n := by
            rw [e1]; push_cast
            have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
            nlinarith
          calc (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ)) * M
              ≤ (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ)) * 2 ^ (alphaC * n) := by
                rw [Real.rpow_natCast]
                exact mul_le_mul_of_nonneg_left hMα (by positivity)
            _ = (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) + H * ((n - j - 1 : ℕ) : ℝ) + alphaC * n) := by
                rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num)]
            _ ≤ (2 : ℝ) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
            _ = 2 ^ n := Real.rpow_natCast 2 n
      _ = m * 2 ^ n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ n * 2 ^ n := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hmn.le
  -- total
  calc (cntRes n M r : ℝ) * M
      ≤ (((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) +
          ∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ))) * M :=
        mul_le_mul_of_nonneg_right hcardR hMpos.le
    _ = ((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) * M +
          (∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ))) * M := by ring
    _ ≤ 4 * n ^ 3 * (n - 1) * 2 ^ n + n * 2 ^ n := add_le_add hnorm hexc
    _ ≤ 4 * n ^ 4 * 2 ^ n := by
        have hp : (0 : ℝ) < 2 ^ n := by positivity
        have h3 : (0 : ℝ) ≤ 4 * n ^ 3 - n := by nlinarith
        have h := mul_nonneg h3 hp.le
        have e : (4 : ℝ) * n ^ 4 * 2 ^ n - (4 * n ^ 3 * (n - 1) * 2 ^ n + n * 2 ^ n) =
            (4 * n ^ 3 - n) * 2 ^ n := by ring
        linarith

end Lagarias
