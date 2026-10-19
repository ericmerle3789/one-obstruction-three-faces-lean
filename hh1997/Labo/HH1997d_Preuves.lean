import Mathlib
import Labo.HH1997d_Enonces
import Labo.HH1997b_Preuves

/-!
# LABO-COLLATZ · HH1997d · formaliste (2026-10-19) — PROOFS of `Labo/HH1997d_Enonces.lean`

Halbeisen–Hungerbühler 1997, §4.1–4.3: Lemma 8, Theorem 1 (conditional), Theorem 2, Theorem 3 (conditional), and the
counterexample to the literal reading of "optimal".  Axiom log: `Labo/HH1997d_Axiomes.lean`.

The paper cites Lemma 8 and Theorems 1–2 without proof.  Proof routes used here:
* product formula: along one period, `2·x_{i+1} = x_i·(3 + 1/x_i)` at odd points and `= x_i` at even points, and the
  product of the `x_i` is invariant under the shift, so `2^l = Π_{odd} (3 + 1/x)`;
* Theorem 2 (Eliahou): `2^l ≤ (3 + 1/min C)^n`, take `log₂`, and `n ≤ n(l)`;
* Lemma 8 (Crandall): `m(2^l − 3^n) ≤ m((3 + 1/m)^n − 3^n) < n(3 + 1/m)^{n−1}` (mean-value bound, strict for `n ≥ 2`);
  `m > 1` is used only to exclude `n ≤ 1`;
* Theorem 1 (Crandall): if `n ≤ q_k` the continued-fraction gap gives `l − nθ > 1/(q_k + q_{k+1})`, hence
  `2^l − 3^n > 3^n log 2 / S`; with Lemma 8 and `n ≤ 2m/S`, `S ≥ 18`, this forces `3 log 2 < 27/13`, false;
* Theorem 3: (11) (`eq11`, batch b) + the displayed line (`thm3_line`, Prop. 2 + Lemma 6), then take `log₂`.
Small rational evaluations in the counterexample use `decide +kernel` (kernel reduction, no extra axiom).
-/

namespace LaboHH

open LaboBP

/-! ## Positivity, steps, the product identity -/

lemma collatzQ_pos {y : ℚ} (hy : 0 < y) : 0 < collatzQ y := by
  unfold collatzQ
  split_ifs <;> positivity

lemma iterate_pos {x₀ : ℚ} (h : 0 < x₀) (i : ℕ) : 0 < collatzQ^[i] x₀ := by
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Function.iterate_succ_apply']; exact collatzQ_pos ih

lemma cycle_pos {x₀ : ℚ} (h : 0 < x₀) : ∀ y ∈ cycle x₀, 0 < y := by
  rintro _ ⟨i, rfl⟩
  exact iterate_pos h i

lemma step_of_orbit (x₀ : ℚ) (w : List Bool)
    (horb : ∀ i, i ≤ w.length → collatzQ^[i] x₀ = phiMap (w.take i) x₀) :
    ∀ i < w.length, collatzQ^[i + 1] x₀ = gStep (w.getD i false) (collatzQ^[i] x₀) := by
  intro i hi
  rw [horb (i + 1) hi, horb i hi.le, List.take_succ_eq_append_getElem hi, phiMap_append_singleton,
    List.getD_eq_getElem _ _ hi]

lemma gStep_mul_two (b : Bool) {y : ℚ} (hy : y ≠ 0) :
    2 * gStep b y = y * (if b then 3 + 1 / y else 1) := by
  cases b
  · simp only [gStep, Bool.false_eq_true, ↓reduceIte]; ring
  · simp only [gStep, ↓reduceIte]
    rw [mul_add, mul_one_div_cancel hy]
    ring

/-- `2^l = Π_{i<l} (3 + 1/x_i if s_i = 1, else 1)` along a periodic orbit of positive points. -/
lemma prod_identity (x : ℕ → ℚ) (w : List Bool)
    (hstep : ∀ i < w.length, x (i + 1) = gStep (w.getD i false) (x i))
    (hper : x w.length = x 0) (hpos : ∀ i < w.length, 0 < x i) :
    (2 : ℚ) ^ w.length = ∏ i ∈ Finset.range w.length, (if w.getD i false then 3 + 1 / x i else 1) := by
  have h1 : ∏ i ∈ Finset.range w.length, (2 * x (i + 1))
      = ∏ i ∈ Finset.range w.length, (x i * (if w.getD i false then 3 + 1 / x i else 1)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hstep i hi']
    exact gStep_mul_two _ (hpos i hi').ne'
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at h1
  have hshift : ∏ i ∈ Finset.range w.length, x (i + 1) = ∏ i ∈ Finset.range w.length, x i := by
    rcases Nat.eq_zero_or_pos w.length with h | h
    · simp [h]
    · have a := Finset.prod_range_succ x w.length
      have b := Finset.prod_range_succ' x w.length
      rw [hper] at a
      exact mul_right_cancel₀ (hpos 0 h).ne' (b.symm.trans a)
  have hP : ∏ i ∈ Finset.range w.length, x i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => (hpos i (Finset.mem_range.mp hi)).ne'
  rw [hshift] at h1
  apply mul_left_cancel₀ hP
  rw [← h1]
  ring

/-- `a^n ≤ Π ≤ r^n` when every factor at a letter `1` lies in `[a, r]`. -/
lemma prod_bounds (w : List Bool) (f : ℕ → ℚ) (a r : ℚ) (ha : 0 ≤ a)
    (hf : ∀ i < w.length, w.getD i false = true → a ≤ f i ∧ f i ≤ r) :
    a ^ w.count true ≤ ∏ i ∈ Finset.range w.length, (if w.getD i false then f i else 1) ∧
    ∏ i ∈ Finset.range w.length, (if w.getD i false then f i else 1) ≤ r ^ w.count true := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w b ih =>
    have hget : ∀ i < w.length, (w ++ [b]).getD i false = w.getD i false :=
      fun i hi => List.getD_append _ _ _ _ hi
    have hlast : (w ++ [b]).getD w.length false = b := by simp
    have hP : ∏ i ∈ Finset.range w.length, (if (w ++ [b]).getD i false then f i else 1)
        = ∏ i ∈ Finset.range w.length, (if w.getD i false then f i else 1) :=
      Finset.prod_congr rfl fun i hi => by rw [hget i (Finset.mem_range.mp hi)]
    obtain ⟨ih1, ih2⟩ := ih fun i hi hb =>
      hf i (by simp only [List.length_append, List.length_singleton]; omega) (by rw [hget i hi]; exact hb)
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ, hP, hlast, List.count_append]
    have hP0 : 0 ≤ ∏ i ∈ Finset.range w.length, (if w.getD i false then f i else 1) :=
      (pow_nonneg ha _).trans ih1
    cases b
    · have hc : [false].count true = 0 := rfl
      simp only [hc, add_zero, Bool.false_eq_true, ↓reduceIte, mul_one]
      exact ⟨ih1, ih2⟩
    · obtain ⟨h1, h2⟩ := hf w.length (by simp) (by rw [hlast])
      have hc : [true].count true = 1 := rfl
      simp only [hc, ↓reduceIte, pow_succ]
      exact ⟨mul_le_mul ih1 h1 ha hP0, mul_le_mul ih2 h2 (ha.trans h1) (hP0.trans ih2)⟩

/-- The product inequality `3^n < 2^l ≤ (3 + 1/m)^n` along the pseudo-cycle of a word, all points `≥ m > 0`. -/
lemma eliahou_core (x₀ m : ℚ) (w : List Bool) (hw : w ≠ [])
    (horb : ∀ i, i ≤ w.length → collatzQ^[i] x₀ = phiMap (w.take i) x₀)
    (hper : collatzQ^[w.length] x₀ = x₀) (hm : 0 < m) (hmin : ∀ i, m ≤ collatzQ^[i] x₀) :
    (3 : ℚ) ^ w.count true < 2 ^ w.length ∧ (2 : ℚ) ^ w.length ≤ (3 + 1 / m) ^ w.count true := by
  have hpos : ∀ i, 0 < collatzQ^[i] x₀ := fun i => hm.trans_le (hmin i)
  have hid := prod_identity (fun i => collatzQ^[i] x₀) w (step_of_orbit x₀ w horb) hper
    (fun i _ => hpos i)
  obtain ⟨hlo, hhi⟩ := prod_bounds w (fun i => 3 + 1 / collatzQ^[i] x₀) 3 (3 + 1 / m) (by norm_num)
    (fun i _ _ => ⟨le_add_of_nonneg_right (by have := hpos i; positivity),
      by linarith [one_div_le_one_div_of_le hm (hmin i)]⟩)
  beta_reduce at hid hlo hhi
  rw [← hid] at hlo hhi
  refine ⟨lt_of_le_of_ne hlo fun h => ?_, hhi⟩
  have h' : 3 ^ w.count true = 2 ^ w.length := by exact_mod_cast h
  have hl : w.length ≠ 0 := fun h0 => hw (List.length_eq_zero_iff.mp h0)
  have he : Even (2 ^ w.length) := (Nat.even_pow' hl).mpr even_two
  rw [← h'] at he
  exact (Nat.not_even_iff_odd.mpr (Odd.pow (by decide))) he

/-! ## The product formula and the product inequality for periodic points -/

lemma cycle_word (x₀ : ℚ) (hper : x₀ ∈ Function.periodicPts collatzQ) :
    parityWord x₀ (Function.minimalPeriod collatzQ x₀) ≠ [] ∧
    (∀ i, i ≤ (parityWord x₀ (Function.minimalPeriod collatzQ x₀)).length →
      collatzQ^[i] x₀ = phiMap ((parityWord x₀ (Function.minimalPeriod collatzQ x₀)).take i) x₀) ∧
    collatzQ^[(parityWord x₀ (Function.minimalPeriod collatzQ x₀)).length] x₀ = x₀ := by
  obtain ⟨hl, horb, -⟩ := lemma1_core x₀ hper
  refine ⟨fun h => ?_, fun i hi => horb i (by simpa using hi), ?_⟩
  · have := congrArg List.length h
    simp at this
    omega
  · rw [parityWord_length]
    exact Function.iterate_minimalPeriod

theorem prod_formula_thm : prod_formula := by
  intro x₀ hper hpos
  obtain ⟨hw, horb, hper'⟩ := cycle_word x₀ hper
  have hid := prod_identity (fun i => collatzQ^[i] x₀) _ (step_of_orbit x₀ _ horb) hper'
    (fun i _ => hpos _ ⟨i, rfl⟩)
  beta_reduce at hid
  rw [parityWord_length] at hid
  rw [hid, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hg : (parityWord x₀ (Function.minimalPeriod collatzQ x₀)).getD i false
      = decide ((collatzQ^[i] x₀).num % 2 ≠ 0) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi')]
    simp [parityWord]
  rw [hg]
  simp only [decide_eq_true_eq]

/-- The data of a positive cycle used by Theorem 2: `m > 0`, `n ≥ 1`, `3^n < 2^l ≤ (3 + 1/m)^n`. -/
lemma cycle_facts (x₀ : ℚ) (hper : x₀ ∈ Function.periodicPts collatzQ) (hpos : ∀ y ∈ cycle x₀, 0 < y)
    (m : ℚ) (hm : IsLeast (cycle x₀) m) :
    0 < m ∧ 1 ≤ (parityWord x₀ (Function.minimalPeriod collatzQ x₀)).count true ∧
    (3 : ℚ) ^ (parityWord x₀ (Function.minimalPeriod collatzQ x₀)).count true
      < 2 ^ Function.minimalPeriod collatzQ x₀ ∧
    (2 : ℚ) ^ Function.minimalPeriod collatzQ x₀
      ≤ (3 + 1 / m) ^ (parityWord x₀ (Function.minimalPeriod collatzQ x₀)).count true := by
  have hm0 : 0 < m := hpos m hm.1
  obtain ⟨hw, horb, hper'⟩ := cycle_word x₀ hper
  obtain ⟨h1, h2⟩ := eliahou_core x₀ m _ hw horb hper' hm0 (fun i => hm.2 ⟨i, rfl⟩)
  rw [parityWord_length] at h1 h2
  refine ⟨hm0, ?_, h1, h2⟩
  rcases Nat.eq_zero_or_pos ((parityWord x₀ (Function.minimalPeriod collatzQ x₀)).count true) with hc | hc
  swap
  · exact hc
  exfalso
  rw [hc, pow_zero] at h2
  have hl := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have : (2 : ℚ) ≤ 2 ^ Function.minimalPeriod collatzQ x₀ := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hl
  linarith

theorem prod_ineq_thm : prod_ineq := by
  intro x₀ hper hpos m hm
  obtain ⟨-, -, h1, h2⟩ := cycle_facts x₀ hper hpos m hm
  exact ⟨h1, h2⟩

/-! ## Theorem 2 (Eliahou) -/

theorem thm2_gen_thm : thm2_gen := by
  intro x₀ hper hpos m hm
  obtain ⟨hm0, hc1, h3, h2⟩ := cycle_facts x₀ hper hpos m hm
  rw [cycle_ncard x₀ hper]
  generalize Function.minimalPeriod collatzQ x₀ = l at h3 h2 hc1 ⊢
  generalize (parityWord x₀ l).count true = c at h3 h2 hc1
  -- c ≤ n(l)
  have h3n : 3 ^ c < 2 ^ l := by exact_mod_cast h3
  have hcn : c ≤ nOf l := by
    rw [nOf_eq_log]
    exact Nat.le_log_of_pow_le (by norm_num) h3n.le
  -- l ≤ c · log₂(3 + 1/m)
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have h2r : (2 : ℝ) ^ l ≤ (3 + 1 / (m : ℝ)) ^ c := by exact_mod_cast h2
  have hlog : (l : ℝ) ≤ c * Real.logb 2 (3 + 1 / (m : ℝ)) := by
    have := (Real.logb_le_logb (b := 2) one_lt_two (by positivity) (by positivity)).mpr h2r
    rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc1
  have hcn' : (c : ℝ) ≤ nOf l := by exact_mod_cast hcn
  apply Nat.sInf_le
  refine ⟨hc1.trans hcn, ?_⟩
  calc (l : ℝ) / nOf l ≤ l / c := div_le_div_of_nonneg_left (Nat.cast_nonneg l) hc0 hcn'
    _ ≤ Real.logb 2 (3 + 1 / (m : ℝ)) := by rw [div_le_iff₀ hc0]; linarith

theorem thm2_thm : thm2 := by
  intro x₀ hx hper m hm
  exact thm2_gen_thm (x₀ : ℚ) hper (cycle_pos (by exact_mod_cast hx)) m hm

/-! ## Lemma 8 (Crandall) -/

lemma phi_pos_of_true : ∀ t : List Bool, true ∈ t → 0 < phi t
  | [], h => by simp at h
  | b :: w, h => by
    rw [phi_cons]
    cases b
    · have hw : true ∈ w := by simpa using h
      have := phi_pos_of_true w hw
      simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      omega
    · simp only [↓reduceIte]
      positivity

lemma pow_sub_pow_le (b r : ℚ) (hb : 0 ≤ b) (hbr : b ≤ r) (k : ℕ) :
    r ^ (k + 1) - b ^ (k + 1) ≤ (k + 1) * r ^ k * (r - b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : b ^ (k + 1) ≤ r ^ (k + 1) := pow_le_pow_left₀ hb hbr _
    have hr : 0 ≤ r := hb.trans hbr
    have e : r ^ (k + 1 + 1) - b ^ (k + 1 + 1)
        = r * (r ^ (k + 1) - b ^ (k + 1)) + b ^ (k + 1) * (r - b) := by ring
    rw [e]
    have h2 := mul_le_mul_of_nonneg_left ih hr
    have h3 := mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hbr)
    push_cast
    calc r * (r ^ (k + 1) - b ^ (k + 1)) + b ^ (k + 1) * (r - b)
        ≤ r * ((k + 1) * r ^ k * (r - b)) + r ^ (k + 1) * (r - b) := add_le_add h2 h3
      _ = (k + 1 + 1) * r ^ (k + 1) * (r - b) := by ring

lemma pow_sub_pow_lt (b r : ℚ) (hb : 0 < b) (hbr : b < r) (k : ℕ) :
    r ^ (k + 2) - b ^ (k + 2) < (k + 2) * r ^ (k + 1) * (r - b) := by
  have ih := pow_sub_pow_le b r hb.le hbr.le k
  have h1 : b ^ (k + 1) < r ^ (k + 1) := pow_lt_pow_left₀ hbr hb.le (by omega)
  have hr : 0 < r := hb.trans hbr
  have e : r ^ (k + 2) - b ^ (k + 2) = r * (r ^ (k + 1) - b ^ (k + 1)) + b ^ (k + 1) * (r - b) := by ring
  rw [e]
  have h2 := mul_le_mul_of_nonneg_left ih hr.le
  have h3 := mul_lt_mul_of_pos_right h1 (sub_pos.mpr hbr)
  calc r * (r ^ (k + 1) - b ^ (k + 1)) + b ^ (k + 1) * (r - b)
      < r * ((k + 1) * r ^ k * (r - b)) + r ^ (k + 1) * (r - b) := add_lt_add_of_le_of_lt h2 h3
    _ = (k + 2) * r ^ (k + 1) * (r - b) := by ring

/-- Lemma 8 for the word `s`, all points `≥ m > 0`, `n ≥ 2`: `m(2^l − 3^n) < n(3 + 1/m)^{n−1}`. -/
lemma lemma8_core (s : List Bool) (hs : s ≠ []) (m : ℚ) (hm : 0 < m)
    (hmin : ∀ i, m ≤ collatzQ^[i] ((phi s : ℚ) / (d s : ℚ))) (hn : 2 ≤ s.count true) :
    m * ((2 : ℚ) ^ s.length - 3 ^ s.count true) < s.count true * (3 + 1 / m) ^ (s.count true - 1) := by
  obtain ⟨-, -, horb, hper⟩ := lemma2_cycle_thm s hs
  obtain ⟨-, hle⟩ := eliahou_core _ m s hs (fun i hi => (horb i hi).1) hper hm hmin
  obtain ⟨k, hk⟩ : ∃ k, s.count true = k + 2 := ⟨s.count true - 2, by omega⟩
  have hlt := pow_sub_pow_lt 3 (3 + 1 / m) (by norm_num) (by linarith [one_div_pos.mpr hm]) k
  rw [hk] at hle ⊢
  rw [show k + 2 - 1 = k + 1 by omega]
  have hr3 : (3 + 1 / m) - 3 = 1 / m := by ring
  rw [hr3] at hlt
  calc m * (2 ^ s.length - 3 ^ (k + 2)) ≤ m * ((3 + 1 / m) ^ (k + 2) - 3 ^ (k + 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hm.le
    _ < m * ((k + 2) * (3 + 1 / m) ^ (k + 1) * (1 / m)) := mul_lt_mul_of_pos_left hlt hm
    _ = ((k + 2 : ℕ) : ℚ) * (3 + 1 / m) ^ (k + 1) := by
        push_cast
        field_simp

/-- The facts behind Lemma 8 (and Theorem 1): `n ≥ 2`, `3^n < 2^l`, `m(2^l − 3^n) < n(3 + 1/m)^{n−1}`. -/
lemma lemma8_facts (l n : ℕ) (s : List Bool) (hS : s ∈ Sln l n) (hnl : n ≤ nOf l) (m : ℚ) (hm1 : 1 < m)
    (hm : IsLeast (cycle ((phi s : ℚ) / (d s : ℚ))) m) :
    2 ≤ n ∧ (3 : ℚ) ^ n < 2 ^ l ∧ m * ((2 : ℚ) ^ l - 3 ^ n) < n * (3 + 1 / m) ^ (n - 1) := by
  obtain ⟨hsl, hsn⟩ := hS
  have hm0 : 0 < m := by linarith
  have hmin : ∀ i, m ≤ collatzQ^[i] ((phi s : ℚ) / (d s : ℚ)) := fun i => hm.2 ⟨i, rfl⟩
  have hs : s ≠ [] := by
    rintro rfl
    have := hmin 0
    simp [phi, phiRev] at this
    linarith
  have hl : 0 < l := by rw [← hsl]; exact List.length_pos_iff.mpr hs
  obtain ⟨-, -, horb, hper⟩ := lemma2_cycle_thm s hs
  obtain ⟨-, hle⟩ := eliahou_core _ m s hs (fun i hi => (horb i hi).1) hper hm0 hmin
  rw [hsl, hsn] at hle
  have hspec := nOf_spec_thm l hl
  have hD : (3 : ℚ) ^ n < 2 ^ l := by
    exact_mod_cast lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hnl) hspec.1
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · exfalso
      interval_cases n
      · rw [pow_zero] at hle
        have : (2 : ℚ) ≤ 2 ^ l := by
          calc (2 : ℚ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl
        linarith
      · rw [pow_one] at hle
        have h3 : 3 < 2 ^ l := lt_of_le_of_lt (by simpa using Nat.pow_le_pow_right (show 0 < 3 by norm_num) hnl)
          hspec.1
        have h4 : (4 : ℚ) ≤ 2 ^ l := by
          have : 4 ≤ 2 ^ l := h3
          exact_mod_cast this
        have : 1 / m < 1 := by rw [div_lt_one hm0]; exact hm1
        linarith
    · exact h
  refine ⟨hn2, hD, ?_⟩
  have key := lemma8_core s hs m hm0 hmin (by rw [hsn]; exact hn2)
  rwa [hsl, hsn] at key

theorem lemma8_thm : lemma8 := by
  intro l n s hS hnl m hm1 hm
  obtain ⟨-, hD, key⟩ := lemma8_facts l n s hS hnl m hm1 hm
  rw [lt_div_iff₀ (by linarith)]
  exact key

theorem lemma8_gen_thm : lemma8_gen := by
  intro l n s hS hn2 hnl m hm
  obtain ⟨hsl, hsn⟩ := hS
  have hs : s ≠ [] := by
    rintro rfl
    simp at hsn
    omega
  have hl : 0 < l := by rw [← hsl]; exact List.length_pos_iff.mpr hs
  have hD : (3 : ℚ) ^ n < 2 ^ l := by
    exact_mod_cast lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hnl) (nOf_spec_thm l hl).1
  have hphi : 0 < phi s := phi_pos_of_true s (List.count_pos_iff.mp (by omega))
  have hdq : (d s : ℚ) = 2 ^ l - 3 ^ n := by rw [← hsl, ← hsn]; simp [LaboBP.d]
  have hx0 : 0 < (phi s : ℚ) / (d s : ℚ) := div_pos (by exact_mod_cast hphi) (by rw [hdq]; linarith)
  have hm0 : 0 < m := cycle_pos hx0 m hm.1
  have key := lemma8_core s hs m hm0 (fun i => hm.2 ⟨i, rfl⟩) (by rw [hsn]; exact hn2)
  rw [hsl, hsn] at key
  rw [lt_div_iff₀ (by linarith)]
  exact key

/-! ## Theorem 1 (Crandall), conditional on the continued-fraction gap -/

lemma theta_irrational : Irrational theta := by
  rintro ⟨q, hq⟩
  have h3 : (2 : ℝ) ^ (q : ℝ) = 3 := by
    rw [hq]
    exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have hmul : (q : ℝ) * q.den = q.num := by
    have := Rat.mul_den_eq_num q
    exact_mod_cast this
  have h4 : (2 : ℝ) ^ (q.num : ℝ) = 3 ^ q.den := by
    rw [← hmul, Real.rpow_mul (by norm_num), h3, Real.rpow_natCast]
  rw [Real.rpow_intCast] at h4
  rcases le_or_gt q.num 0 with hn | hn
  · have h5 : (2 : ℝ) ^ q.num ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hn
    have h6 : (3 : ℝ) ≤ 3 ^ q.den := le_self_pow₀ (by norm_num) q.pos.ne'
    linarith
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn.le
    rw [hk, zpow_natCast] at h4
    have h5 : 2 ^ k = 3 ^ q.den := by exact_mod_cast h4
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk, Nat.cast_zero] at hn
      exact lt_irrefl 0 hn
    have he : Even (3 ^ q.den) := h5 ▸ (Nat.even_pow' hk0).mpr even_two
    exact (Nat.not_even_iff_odd.mpr (Odd.pow (by decide))) he

lemma theta_not_terminated (n : ℕ) : ¬ (GenContFract.of theta).TerminatedAt n := by
  intro h
  obtain ⟨q, hq⟩ := (GenContFract.terminates_iff_rat theta).mp ⟨n, h⟩
  exact theta_irrational ⟨q, hq.symm⟩

lemma qCF_ge_fib (k : ℕ) : (Nat.fib (k + 1) : ℝ) ≤ qCF k :=
  GenContFract.succ_nth_fib_le_of_nth_den (Or.inr (theta_not_terminated _))

theorem cf_size_thm : cf_size := by
  intro k hk
  have h1 : (8 : ℝ) ≤ qCF k := by
    have h : 8 ≤ Nat.fib (k + 1) := (show Nat.fib 6 = 8 by decide) ▸ Nat.fib_mono (by omega)
    exact le_trans (by exact_mod_cast h) (qCF_ge_fib k)
  have h2 : (13 : ℝ) ≤ qCF (k + 1) := by
    have h : 13 ≤ Nat.fib (k + 1 + 1) := (show Nat.fib 7 = 13 by decide) ▸ Nat.fib_mono (by omega)
    exact le_trans (by exact_mod_cast h) (qCF_ge_fib (k + 1))
  linarith

/-- The analytic heart of Theorem 1. -/
lemma thm1_analytic (m : ℝ) (n l : ℕ) (S : ℝ) (hm : 1 < m) (hS : 18 ≤ S)
    (hgap : 1 / S < (l : ℝ) - n * theta)
    (key : m * ((2 : ℝ) ^ l - 3 ^ n) < n * (3 + 1 / m) ^ (n - 1)) (hn : 1 ≤ n)
    (hnS : (n : ℝ) * S ≤ 2 * m) : False := by
  have hm0 : 0 < m := by linarith
  have hSpos : 0 < S := by linarith
  have L2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  -- 2^l = 3^n · 2^{l − nθ} ≥ 3^n (1 + log 2 · (l − nθ))
  have h2θ : (2 : ℝ) ^ theta = 3 := Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have hpow : (2 : ℝ) ^ ((l : ℝ) - n * theta) * 3 ^ n = 2 ^ l := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, mul_comm (n : ℝ) theta, Real.rpow_mul (by norm_num),
      h2θ, Real.rpow_natCast]
    field_simp
  have hexp : 1 + Real.log 2 * ((l : ℝ) - n * theta) ≤ (2 : ℝ) ^ ((l : ℝ) - n * theta) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    linarith [Real.add_one_le_exp (Real.log 2 * ((l : ℝ) - n * theta))]
  have h3n : (0 : ℝ) < 3 ^ n := by positivity
  have hlow : (3 : ℝ) ^ n * (Real.log 2 / S) < 2 ^ l - 3 ^ n := by
    have h1 : Real.log 2 / S < Real.log 2 * ((l : ℝ) - n * theta) := by
      rw [div_eq_mul_one_div]
      exact mul_lt_mul_of_pos_left hgap (by linarith)
    have e1 := mul_le_mul_of_nonneg_left hexp h3n.le
    have e2 := mul_lt_mul_of_pos_left h1 h3n
    nlinarith [e1, e2, hpow]
  -- (3 + 1/m)^{n−1} ≤ 3^{n−1} · 27/26
  have ht : 0 < 1 / (3 * m) := by positivity
  have hfac : (3 + 1 / m) = 3 * (1 + 1 / (3 * m)) := by field_simp
  have hb1 : (1 + 1 / (3 * m)) ^ (n - 1) ≤ Real.exp (((n - 1 : ℕ) : ℝ) * (1 / (3 * m))) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (3 * m))]) _
  have hn_le : (n : ℝ) ≤ m / 9 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg (α := ℝ) n)]
  have hsmall : ((n - 1 : ℕ) : ℝ) * (1 / (3 * m)) ≤ 1 / 27 := by
    have h1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    calc ((n - 1 : ℕ) : ℝ) * (1 / (3 * m)) ≤ (m / 9) * (1 / (3 * m)) :=
          mul_le_mul_of_nonneg_right (h1.trans hn_le) ht.le
      _ = 1 / 27 := by field_simp; ring
  have hexp27 : Real.exp (1 / 27) ≤ 27 / 26 := by
    have := Real.exp_bound_div_one_sub_of_interval (show (0 : ℝ) ≤ 1 / 27 by norm_num) (by norm_num)
    norm_num at this ⊢
    linarith
  have hbound : (1 + 1 / (3 * m)) ^ (n - 1) ≤ 27 / 26 :=
    hb1.trans ((Real.exp_le_exp.mpr hsmall).trans hexp27)
  have hr : (3 + 1 / m) ^ (n - 1) ≤ 3 ^ (n - 1) * (27 / 26) := by
    rw [hfac, mul_pow]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  have h3 : (3 : ℝ) ^ n = 3 * 3 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hA : m * ((3 : ℝ) ^ n * (Real.log 2 / S)) < n * (3 ^ (n - 1) * (27 / 26)) := by
    calc m * ((3 : ℝ) ^ n * (Real.log 2 / S)) < m * (2 ^ l - 3 ^ n) := mul_lt_mul_of_pos_left hlow hm0
      _ < n * (3 + 1 / m) ^ (n - 1) := key
      _ ≤ n * (3 ^ (n - 1) * (27 / 26)) := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg n)
  rw [h3] at hA
  have hp : (0 : ℝ) < 3 ^ (n - 1) := by positivity
  have hB : m * (3 * (Real.log 2 / S)) < n * (27 / 26) := by
    have hA' : 3 ^ (n - 1) * (m * (3 * (Real.log 2 / S))) < 3 ^ (n - 1) * (n * (27 / 26)) := by
      nlinarith [hA]
    exact lt_of_mul_lt_mul_left hA' hp.le
  have hC : 3 * m * Real.log 2 < n * S * (27 / 26) := by
    have := mul_lt_mul_of_pos_right hB hSpos
    have e : m * (3 * (Real.log 2 / S)) * S = 3 * m * Real.log 2 := by field_simp
    rw [e] at this
    linarith
  have hD := mul_lt_mul_of_pos_left L2 hm0
  nlinarith [hC, hnS, hD]

theorem thm1_cond_thm : thm1_cond := by
  intro hgap h45 k hk l n s hS hnl m hm1 hm
  obtain ⟨hn2, hD, key⟩ := lemma8_facts l n s hS hnl m hm1 hm
  by_contra hcon
  obtain ⟨hnq, hn2m⟩ := le_min_iff.mp (not_lt.mp hcon)
  have hS18 : 18 ≤ qCF k + qCF (k + 1) := by
    rcases (show k = 4 ∨ 5 ≤ k by omega) with rfl | h
    · exact h45
    · exact cf_size_thm k h
  have hSpos : 0 < qCF k + qCF (k + 1) := by linarith
  have hg := hgap k hk (l : ℤ) (n : ℤ) (by exact_mod_cast (show 1 ≤ n by omega)) (by exact_mod_cast hnq)
  push_cast at hg
  -- nθ < l
  have hD' : (3 : ℝ) ^ n < 2 ^ l := by exact_mod_cast hD
  have hθ : (n : ℝ) * theta < l := by
    have := Real.logb_lt_logb (b := 2) one_lt_two (by positivity) hD'
    rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
  rw [abs_sub_comm, abs_of_pos (by linarith)] at hg
  have key' : (m : ℝ) * ((2 : ℝ) ^ l - 3 ^ n) < n * (3 + 1 / (m : ℝ)) ^ (n - 1) := by exact_mod_cast key
  have hnS : (n : ℝ) * (qCF k + qCF (k + 1)) ≤ 2 * m := by
    rwa [le_div_iff₀ hSpos] at hn2m
  exact thm1_analytic m n l _ (by exact_mod_cast hm1) hS18 hg key' (by omega) hnS

/-! ## Theorem 3 (Eliahou improved), conditional on the displayed line -/

lemma nOf_pos_of_two_le {l : ℕ} (hl : 2 ≤ l) : 1 ≤ nOf l := by
  rcases Nat.eq_zero_or_pos (nOf l) with h0 | h0
  swap
  · exact h0
  exfalso
  have h2 := (nOf_spec_thm l (by omega)).2
  rw [h0, zero_add, pow_one] at h2
  have : 4 ≤ 2 ^ l := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
  omega

theorem thm3_last_thm : thm3_last := by
  intro hline x₀ hodd hper hpos hlen m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm.1
  obtain ⟨-, h1, h2⟩ := eq11_thm x₀ hodd hper hpos m hm _ _ rfl rfl
  rw [cycle_ncard x₀ hper] at hlen ⊢
  generalize Function.minimalPeriod collatzQ x₀ = l at h1 h2 hlen ⊢
  have hq : (m : ℝ) ≤ (M l (nOf l) : ℝ) / ((2 : ℝ) ^ l - 3 ^ nOf l) := by exact_mod_cast h1.trans h2
  have hle := hq.trans (hline l hlen)
  have hn1 : 1 ≤ nOf l := nOf_pos_of_two_le (by omega)
  have hn0 : (nOf l : ℝ) ≠ 0 := by exact_mod_cast (show nOf l ≠ 0 by omega)
  have hTn : ((2 : ℝ) ^ ((l : ℝ) / nOf l)) ^ nOf l = 2 ^ l := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hn0, Real.rpow_natCast]
  have h3n : (3 : ℝ) ^ nOf l < 2 ^ l := by exact_mod_cast (nOf_spec_thm l (by omega)).1
  have hT3 : 3 < (2 : ℝ) ^ ((l : ℝ) / nOf l) := by
    rw [← hTn] at h3n
    exact (pow_lt_pow_iff_left₀ (by norm_num) (by positivity) (by omega)).mp h3n
  rw [← div_eq_mul_inv, le_div_iff₀ (sub_pos.mpr hT3)] at hle
  have hT : (2 : ℝ) ^ ((l : ℝ) / nOf l) ≤ 3 + alphaHH / m := by
    have : ((2 : ℝ) ^ ((l : ℝ) / nOf l) - 3) * m ≤ alphaHH := by linarith
    rw [← sub_le_iff_le_add', le_div_iff₀ hm0]
    exact this
  have := (Real.logb_le_logb (b := 2) one_lt_two (by positivity) (by unfold alphaHH; positivity)).mpr hT
  rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this

theorem thm3_cond_thm : thm3_cond := by
  intro hline x₀ hodd hper hpos hlen m hm
  have h := thm3_last_thm hline x₀ hodd hper hpos hlen m hm
  apply Nat.sInf_le
  refine ⟨nOf_pos_of_two_le (by omega), ?_⟩
  rwa [one_div_div]

/-! ## The literal counterexample to "optimal" (length 3) -/

lemma cq1 : collatzQ (1 / 5) = 4 / 5 := by decide +kernel
lemma cq2 : collatzQ (4 / 5) = 2 / 5 := by decide +kernel
lemma cq3 : collatzQ (2 / 5) = 1 / 5 := by decide +kernel

lemma cycle_three (x₀ : ℚ) (hper : x₀ ∈ Function.periodicPts collatzQ)
    (h3 : Function.minimalPeriod collatzQ x₀ = 3) :
    cycle x₀ = {x₀, collatzQ x₀, collatzQ (collatzQ x₀)} := by
  rw [cycle_eq x₀ hper, h3]
  ext y
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    interval_cases a
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩

lemma fifth_periodic : (1 / 5 : ℚ) ∈ Function.periodicPts collatzQ :=
  ⟨3, by norm_num, show collatzQ (collatzQ (collatzQ (1 / 5))) = 1 / 5 by rw [cq1, cq2, cq3]⟩

lemma fifth_period : Function.minimalPeriod collatzQ (1 / 5 : ℚ) = 3 := by
  have hdvd : Function.minimalPeriod collatzQ (1 / 5 : ℚ) ∣ 3 :=
    Function.IsPeriodicPt.minimalPeriod_dvd
      (show collatzQ (collatzQ (collatzQ (1 / 5))) = 1 / 5 by rw [cq1, cq2, cq3])
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    have hfix := Function.minimalPeriod_eq_one_iff_isFixedPt.mp h
    have : collatzQ (1 / 5 : ℚ) = 1 / 5 := hfix
    rw [cq1] at this
    norm_num at this
  · exact h

lemma fifth_cycle : cycle (1 / 5 : ℚ) = {1 / 5, 2 / 5, 4 / 5} := by
  rw [cycle_three _ fifth_periodic fifth_period, cq1, cq2]
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

lemma fifth_least : IsLeast ({1 / 5, 2 / 5, 4 / 5} : Set ℚ) (1 / 5) := by
  refine ⟨by simp, ?_⟩
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl <;> norm_num

lemma nOf_one : nOf 1 = 0 := by
  have h := (nOf_spec_thm 1 one_pos).1
  by_contra h0
  have : 3 ≤ 3 ^ nOf 1 := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ nOf 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma nOf_two : nOf 2 = 1 := by
  obtain ⟨h1, h2⟩ := nOf_spec_thm 2 two_pos
  rcases Nat.lt_or_ge (nOf 2) 1 with h | h
  · have h0 : nOf 2 = 0 := by omega
    rw [h0] at h2
    norm_num at h2
  · rcases Nat.lt_or_ge (nOf 2) 2 with h' | h'
    · omega
    · have : 9 ≤ 3 ^ nOf 2 := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ nOf 2 := Nat.pow_le_pow_right (by norm_num) h'
      norm_num at h1
      omega

lemma Q4_zero : Q4 0 = 0 := by simp [Q4]

lemma Q4_one : Q4 1 = 0 := by
  unfold Q4
  rw [nOf_one]
  simp [cl]

lemma Q4_two : Q4 2 = 1 := by
  unfold Q4
  rw [nOf_two]
  have c1 : cl 2 1 1 = 1 := by
    have a := (cl_le_iff (l := 2) (n := 1) (j := 1) (k := 1) two_pos).mpr (by norm_num)
    have b := (cl_le_iff (l := 2) (n := 1) (j := 1) (k := 0) two_pos).not.mpr (by norm_num)
    omega
  have c2 : cl 2 1 2 = 1 := by
    have a := (cl_le_iff (l := 2) (n := 1) (j := 2) (k := 1) two_pos).mpr (by norm_num)
    have b := (cl_le_iff (l := 2) (n := 1) (j := 2) (k := 0) two_pos).not.mpr (by norm_num)
    omega
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc, Finset.sum_pair (by norm_num)]
  simp [c1, c2, cl_zero]
  norm_num

lemma Lm_fifth : Lm (1 / 5) = 2 := by
  unfold Lm
  have h2 : (2 : ℕ) ∈ {L : ℕ | (1 / 5 : ℚ) ≤ Q4 L} := by
    show (1 / 5 : ℚ) ≤ Q4 2
    rw [Q4_two]
    norm_num
  apply le_antisymm (Nat.sInf_le h2)
  have hmem := Nat.sInf_mem ⟨2, h2⟩
  by_contra hlt
  have hlt' := not_le.mp hlt
  have : sInf {L : ℕ | (1 / 5 : ℚ) ≤ Q4 L} = 0 ∨ sInf {L : ℕ | (1 / 5 : ℚ) ≤ Q4 L} = 1 := by omega
  rcases this with h | h <;> rw [h] at hmem
  · have h0 : (1 / 5 : ℚ) ≤ Q4 0 := hmem
    rw [Q4_zero] at h0; norm_num at h0
  · have h1 : (1 / 5 : ℚ) ≤ Q4 1 := hmem
    rw [Q4_one] at h1; norm_num at h1

theorem opt_counterexample_thm : opt_counterexample := by
  refine ⟨⟨by decide +kernel, fifth_periodic, cycle_pos (by norm_num), fifth_cycle, ?_, Lm_fifth⟩, ?_⟩
  · rw [cycle_ncard _ fifth_periodic, fifth_period]
  intro x₀ hodd hper hpos hcard
  have h3 : Function.minimalPeriod collatzQ x₀ = 3 := (cycle_ncard x₀ hper).symm.trans hcard
  obtain ⟨m₀, hm₀⟩ := cycle_min_exists x₀ hper
  obtain ⟨-, hc1, hD, -⟩ := cycle_facts x₀ hper hpos m₀ hm₀
  obtain ⟨-, -, hx⟩ := lemma1_core x₀ hper
  rw [h3] at hc1 hD hx
  have hc : (parityWord x₀ 3).count true = 1 := by
    by_contra hne
    have h2 : 2 ≤ (parityWord x₀ 3).count true := by omega
    have : (3 : ℚ) ^ 2 ≤ 3 ^ (parityWord x₀ 3).count true := pow_le_pow_right₀ (by norm_num) h2
    norm_num at hD this
    linarith
  obtain ⟨a, b, c, hw⟩ := List.length_eq_three.mp (parityWord_length x₀ 3)
  rw [hw] at hc hx
  have hx3 : x₀ = 1 / 5 ∨ x₀ = 2 / 5 ∨ x₀ = 4 / 5 := by
    cases a <;> cases b <;> cases c <;> simp at hc <;> simp [phi, phiRev, LaboBP.d] at hx <;> norm_num [hx]
  have hcyc : cycle x₀ = {1 / 5, 2 / 5, 4 / 5} := by
    rw [cycle_three x₀ hper h3]
    rcases hx3 with rfl | rfl | rfl
    · rw [cq1, cq2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    · rw [cq3, cq1]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    · rw [cq2, cq3]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨hcyc, fun m hm => ?_⟩
  rw [hcyc] at hm
  rw [hm.unique fifth_least, Lm_fifth, hcard]
  norm_num

end LaboHH
