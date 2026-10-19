import Mathlib
import Labo.HH1997c_Enonces
import Labo.HH1997b_Preuves

/-!
# LABO-COLLATZ · HH1997c · formaliste (2026-10-19) — PROOFS of `Labo/HH1997c_Enonces.lean`

Third batch of Halbeisen–Hungerbühler 1997: Prop. 1, Prop. 2, Lemma 6, Remark 1, the sign clause of Lemma 1,
the reduction of the numerical example of §4.4.  Axiom log: `Labo/HH1997c_Axiomes.lean`.
Reused: the first batch (`cor1_thm`, `lemma5` toolkit `cl_*`, `wt`, `stilde_*`, `phi_cons`, `orbit_formula`) and the
second batch (`nOf_spec_thm`, `nOf_le`, `lemma1_core`, `cycle_point_aux`, `cycle_ncard`, `cycle_min_exists`,
`thm4_core_thm`, `M_eq_phi_stilde`).
-/

namespace LaboHH

open LaboBP

/-! ## Lemma 1, last sentence -/

theorem zero_cycle_thm : zero_cycle := by
  simp [zero_cycle, collatzQ]

lemma phi_pos_iff (s : List Bool) : 0 < phi s ↔ true ∈ s := by
  induction s with
  | nil => simp
  | cons b w ih =>
    rw [phi_cons]
    cases b
    · simp [ih]
    · simp only [↓reduceIte, List.mem_cons, true_or, iff_true]
      positivity

theorem lemma1_sign_thm : lemma1_sign := by
  intro x₀ _ hper hx0
  obtain ⟨hp, horb, hx⟩ := lemma1_core x₀ hper
  set p := Function.minimalPeriod collatzQ x₀ with hpdef
  set w := parityWord x₀ p with hwdef
  have hwl : w.length = p := by simp [w]
  have hw : w ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [hwl] at this
    simp at this
    omega
  have horb' : ∀ i, i ≤ w.length → collatzQ^[i] x₀ = phiMap (w.take i) x₀ := fun i hi =>
    horb i (by rw [hwl] at hi; exact hi)
  have hpt : ∀ y ∈ cycle x₀, ∃ i, y = (phi (w.rotate i) : ℚ) / (d w : ℚ) := by
    rintro y ⟨j, rfl⟩
    refine ⟨j % p, ?_⟩
    show collatzQ^[j] x₀ = _
    rw [← Function.iterate_mod_minimalPeriod_eq]
    exact cycle_point_aux x₀ w hw horb' hx (j % p) (by rw [hwl]; exact (Nat.mod_lt _ hp).le)
  have htrue : true ∈ w := by
    by_contra h
    apply hx0
    rw [hx]
    have : phi w = 0 := by
      by_contra h0
      exact h ((phi_pos_iff w).mp (Nat.pos_of_ne_zero h0))
    simp [this]
  have hdne : (d w : ℚ) ≠ 0 := by exact_mod_cast d_ne_zero w hw
  have hphi : ∀ i, (0 : ℚ) < phi (w.rotate i) := fun i => by
    exact_mod_cast (phi_pos_iff _).mpr (List.mem_rotate.mpr htrue)
  rcases lt_or_gt_of_ne hdne with hneg | hpos
  · right
    intro y hy
    obtain ⟨i, rfl⟩ := hpt y hy
    exact div_neg_of_pos_of_neg (hphi i) hneg
  · left
    intro y hy
    obtain ⟨i, rfl⟩ := hpt y hy
    exact div_pos (hphi i) hpos

/-! ## Tools: `r = 3^{n/l}`, the sum of Corollary 1 over `range l`, an Abel inequality -/

/-- `r = 3^{n/l}`. -/
noncomputable def rr (l n : ℕ) : ℝ := (3 : ℝ) ^ ((n : ℝ) / l)

lemma rr_pos (l n : ℕ) : 0 < rr l n := by unfold rr; positivity

lemma rr_pow (l n k : ℕ) : rr l n ^ k = (3 : ℝ) ^ ((k * n : ℝ) / l) := by
  rw [rr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

lemma rr_pow_l {l : ℕ} (n : ℕ) (hl : 0 < l) : rr l n ^ l = 3 ^ n := by
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [rr_pow, show ((l : ℝ) * n) / l = n by field_simp, Real.rpow_natCast]

lemma rr_lt_two {l n : ℕ} (hl : 0 < l) (h3 : 3 ^ n < 2 ^ l) : rr l n < 2 := by
  have h3R : (3 : ℝ) ^ n < 2 ^ l := by exact_mod_cast h3
  exact lt_of_pow_lt_pow_left₀ l (by norm_num) (by rw [rr_pow_l n hl]; exact h3R)

lemma three_pow_lt_of_le_nOf {l n : ℕ} (hl : 0 < l) (hn : n ≤ nOf l) : 3 ^ n < 2 ^ l :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hn) (nOf_spec_thm l hl).1

lemma cl_ge (l n j : ℕ) : ((j * n : ℝ) / l) ≤ cl l n j := by
  have h := Nat.le_ceil ((((j * n : ℕ)) : ℚ) / l)
  have h' : (((((j * n : ℕ)) : ℚ) / l : ℚ) : ℝ) ≤ ((cl l n j : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

lemma cl_lt (l n j : ℕ) : (cl l n j : ℝ) < (j * n : ℝ) / l + 1 := by
  have h := Nat.ceil_lt_add_one (by positivity : (0 : ℚ) ≤ (((j * n : ℕ)) : ℚ) / l)
  have h' : ((cl l n j : ℕ) : ℝ) < (((((j * n : ℕ)) : ℚ) / l + 1 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

/-- Corollary 1 over `range l`. -/
lemma M_range {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) :
    M l n = ∑ j ∈ Finset.range l, (cl l n (j + 1) - cl l n j) * 2 ^ j * 3 ^ (n - cl l n (j + 1)) := by
  rw [cor1_thm l n hl hn, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 1 + j - 1 = j by omega, show 1 + j = j + 1 by omega]

lemma M_range_real {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) :
    (M l n : ℝ) = ∑ j ∈ Finset.range l,
      ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) * (2 : ℝ) ^ j * (3 : ℝ) ^ (n - cl l n (j + 1)) := by
  rw [M_range hl hn]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- The jumps of `⌈jn/l⌉` add up: `Σ_{j<k} (⌈(j+1)n/l⌉ − ⌈jn/l⌉) = ⌈kn/l⌉`. -/
lemma sum_jumps (l n k : ℕ) :
    ∑ j ∈ Finset.range k, ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) = cl l n k := by
  rw [Finset.sum_congr rfl fun j _ => Nat.cast_sub (cl_mono l n (Nat.le_succ j)),
    Finset.sum_range_sub (fun j => (cl l n j : ℝ)) k, cl_zero]
  simp

/-- Abel inequality: with non-decreasing weights, prefix sums above the density `δ` and total `L δ`,
the weighted sum is at most `δ · Σ w`. -/
lemma abel_le (L : ℕ) (c w : ℕ → ℝ) (δ : ℝ) (hw : ∀ k, w k ≤ w (k + 1))
    (hpre : ∀ k, k ≤ L → (k : ℝ) * δ ≤ ∑ j ∈ Finset.range k, c j)
    (htot : ∑ j ∈ Finset.range L, c j = L * δ) :
    ∑ j ∈ Finset.range L, c j * w j ≤ δ * ∑ j ∈ Finset.range L, w j := by
  have key : ∀ k, k ≤ L →
      ∑ j ∈ Finset.range k, (c j - δ) * w j ≤ (∑ j ∈ Finset.range k, (c j - δ)) * w k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hE : 0 ≤ ∑ j ∈ Finset.range (k + 1), (c j - δ) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        linarith [hpre (k + 1) hk]
      have ih' := ih (by omega)
      calc ∑ j ∈ Finset.range (k + 1), (c j - δ) * w j
          = ∑ j ∈ Finset.range k, (c j - δ) * w j + (c k - δ) * w k := Finset.sum_range_succ _ _
        _ ≤ (∑ j ∈ Finset.range k, (c j - δ)) * w k + (c k - δ) * w k := by linarith
        _ = (∑ j ∈ Finset.range (k + 1), (c j - δ)) * w k := by rw [Finset.sum_range_succ]; ring
        _ ≤ (∑ j ∈ Finset.range (k + 1), (c j - δ)) * w (k + 1) := mul_le_mul_of_nonneg_left (hw k) hE
  have h := key L le_rfl
  have hE0 : ∑ j ∈ Finset.range L, (c j - δ) = 0 := by
    rw [Finset.sum_sub_distrib, htot]
    simp
  rw [hE0, zero_mul] at h
  have hsplit : ∑ j ∈ Finset.range L, (c j - δ) * w j
      = ∑ j ∈ Finset.range L, c j * w j - δ * ∑ j ∈ Finset.range L, w j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  linarith

/-- `2·Σ_{j<L} v^j ≤ L(1 + v^{L−1})` for `v ≥ 1` (pair `j` with `L − 1 − j`). -/
lemma two_mul_geom_le (v : ℝ) (hv : 1 ≤ v) (L : ℕ) :
    2 * ∑ j ∈ Finset.range L, v ^ j ≤ L * (1 + v ^ (L - 1)) := by
  have hrefl := Finset.sum_range_reflect (fun j => v ^ j) L
  have h2 : 2 * ∑ j ∈ Finset.range L, v ^ j = ∑ j ∈ Finset.range L, (v ^ j + v ^ (L - 1 - j)) := by
    rw [Finset.sum_add_distrib, hrefl]
    ring
  rw [h2]
  have hterm : ∀ j ∈ Finset.range L, v ^ j + v ^ (L - 1 - j) ≤ 1 + v ^ (L - 1) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have h1 : 1 ≤ v ^ j := one_le_pow₀ hv
    have h2 : 1 ≤ v ^ (L - 1 - j) := one_le_pow₀ hv
    have hprod : v ^ j * v ^ (L - 1 - j) = v ^ (L - 1) := by rw [← pow_add]; congr 1; omega
    nlinarith
  calc ∑ j ∈ Finset.range L, (v ^ j + v ^ (L - 1 - j)) ≤ ∑ _j ∈ Finset.range L, (1 + v ^ (L - 1)) :=
        Finset.sum_le_sum hterm
    _ = L * (1 + v ^ (L - 1)) := by simp; ring

/-! ## Proposition 1 -/

lemma term_upper {l n : ℕ} (_hl : 0 < l) (j : ℕ) (hcl : cl l n (j + 1) ≤ n) :
    (2 : ℝ) ^ j * (3 : ℝ) ^ (n - cl l n (j + 1)) ≤ 3 ^ n * (2 ^ j / rr l n ^ (j + 1)) := by
  rw [pow_sub₀ (3 : ℝ) (by norm_num) hcl]
  have h3c : rr l n ^ (j + 1) ≤ (3 : ℝ) ^ (cl l n (j + 1)) := by
    rw [rr_pow, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := cl_ge l n (j + 1)
    push_cast at this ⊢
    exact this
  have hpos : 0 < rr l n ^ (j + 1) := pow_pos (rr_pos l n) _
  have : (2 : ℝ) ^ j * (3 ^ n * (3 ^ cl l n (j + 1))⁻¹) = 3 ^ n * (2 ^ j / 3 ^ cl l n (j + 1)) := by ring
  rw [this]
  gcongr

theorem prop1_thm : prop1 := by
  intro l n hn
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h0 : nOf 0 = 0 := by simp [nOf]
    have : n = 0 := by omega
    subst this
    simp
  have hnl : n ≤ l := hn.trans (nOf_le l)
  have h3 := three_pow_lt_of_le_nOf hl hn
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hr0 := rr_pos l n
  have hr2 := rr_lt_two hl h3
  have h3R : (3 : ℝ) ^ n < 2 ^ l := by exact_mod_cast h3
  have hD : (0 : ℝ) < 2 ^ l - 3 ^ n := by linarith
  set r := rr l n with hr
  set c : ℕ → ℝ := fun j => ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) with hc
  set w : ℕ → ℝ := fun j => 2 ^ j / r ^ (j + 1) with hw
  have hc0 : ∀ j, 0 ≤ c j := fun j => Nat.cast_nonneg _
  have hM : (M l n : ℝ) ≤ 3 ^ n * ∑ j ∈ Finset.range l, c j * w j := by
    rw [M_range_real hl hnl, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have hcl : cl l n (j + 1) ≤ n := (cl_mono l n (by omega : j + 1 ≤ l)).trans (cl_l hl).le
    have := term_upper hl j hcl
    calc c j * 2 ^ j * 3 ^ (n - cl l n (j + 1)) = c j * (2 ^ j * 3 ^ (n - cl l n (j + 1))) := by ring
      _ ≤ c j * (3 ^ n * (2 ^ j / r ^ (j + 1))) := mul_le_mul_of_nonneg_left this (hc0 j)
      _ = 3 ^ n * (c j * w j) := by simp only [hw]; ring
  have hwmono : ∀ k, w k ≤ w (k + 1) := by
    intro k
    simp only [hw]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : (2 : ℝ) ^ k * r ^ (k + 1 + 1) = (2 ^ k * r ^ (k + 1)) * r := by ring
    have e2 : (2 : ℝ) ^ (k + 1) * r ^ (k + 1) = (2 ^ k * r ^ (k + 1)) * 2 := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hr2.le (by positivity)
  have hpre : ∀ k, k ≤ l → (k : ℝ) * ((n : ℝ) / l) ≤ ∑ j ∈ Finset.range k, c j := by
    intro k _
    simp only [hc]
    rw [sum_jumps]
    have := cl_ge l n k
    calc (k : ℝ) * ((n : ℝ) / l) = (k * n : ℝ) / l := by ring
      _ ≤ _ := this
  have htot : ∑ j ∈ Finset.range l, c j = l * ((n : ℝ) / l) := by
    simp only [hc]
    rw [sum_jumps, cl_l hl]
    field_simp
  have habel := abel_le l c w ((n : ℝ) / l) hwmono hpre htot
  have hgeom : ∑ j ∈ Finset.range l, w j = ((2 : ℝ) ^ l / 3 ^ n - 1) / (2 - r) := by
    have hq : (2 / r) ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq hr0.ne'] at h
      linarith
    have hwj : ∀ j, w j = (1 / r) * (2 / r) ^ j := fun j => by
      simp only [hw]
      rw [div_pow, pow_succ]
      field_simp
    rw [Finset.sum_congr rfl (fun j _ => hwj j), ← Finset.mul_sum, geom_sum_eq hq, div_pow, rr_pow_l n hl]
    have h2r : (2 : ℝ) - r ≠ 0 := by linarith
    field_simp
  rw [div_le_iff₀ hD]
  calc (M l n : ℝ) ≤ 3 ^ n * ∑ j ∈ Finset.range l, c j * w j := hM
    _ ≤ 3 ^ n * ((n : ℝ) / l * ∑ j ∈ Finset.range l, w j) := by gcongr
    _ = (n : ℝ) / l * (1 / (2 - r)) * (2 ^ l - 3 ^ n) := by
      rw [hgeom]
      have h2r : (2 : ℝ) - r ≠ 0 := by linarith
      have h3n : (3 : ℝ) ^ n ≠ 0 := by positivity
      field_simp

/-! ## Remark 1 -/

lemma nOf_pos {l : ℕ} (hl : 2 ≤ l) : 1 ≤ nOf l := by
  by_contra h
  have h0 : nOf l = 0 := by omega
  have := (nOf_spec_thm l (by omega)).2
  rw [h0] at this
  have h4 : 2 ^ 2 ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
  omega

theorem remark1_lower6_thm : remark1_lower6 := by
  intro l hl2
  have hl : 0 < l := by omega
  set n := nOf l with hndef
  have hn1 := nOf_pos hl2
  have hnl : n ≤ l := nOf_le l
  have h3 := three_pow_lt_of_le_nOf hl (le_refl n)
  have hr0 := rr_pos l n
  have hr2 := rr_lt_two hl h3
  set r := rr l n with hr
  have hlow : (n : ℝ) * 3 ^ n / 6 ≤ M l n := by
    rw [M_range_real hl hnl]
    have hterm : ∀ j ∈ Finset.range l, ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) * (3 ^ n / 6)
        ≤ ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) * (2 : ℝ) ^ j * (3 : ℝ) ^ (n - cl l n (j + 1)) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hcl : cl l n (j + 1) ≤ n := (cl_mono l n (by omega : j + 1 ≤ l)).trans (cl_l hl).le
      have h3c : (3 : ℝ) ^ (cl l n (j + 1)) ≤ 3 * r ^ (j + 1) := by
        rw [rr_pow, ← Real.rpow_natCast]
        calc (3 : ℝ) ^ ((cl l n (j + 1) : ℕ) : ℝ) ≤ (3 : ℝ) ^ (((j + 1 : ℕ) * n : ℝ) / l + 1) := by
              apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
              exact (cl_lt l n (j + 1)).le
          _ = 3 * (3 : ℝ) ^ (((j + 1 : ℕ) * n : ℝ) / l) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
      have hge : (3 : ℝ) ^ n / 6 ≤ (2 : ℝ) ^ j * (3 : ℝ) ^ (n - cl l n (j + 1)) := by
        have hpos : 0 < (3 : ℝ) ^ (cl l n (j + 1)) := by positivity
        have e : (2 : ℝ) ^ j * (3 : ℝ) ^ (n - cl l n (j + 1)) = 3 ^ n * 2 ^ j / 3 ^ cl l n (j + 1) := by
          rw [pow_sub₀ (3 : ℝ) (by norm_num) hcl]; field_simp
        rw [e, div_le_div_iff₀ (by norm_num) hpos]
        have hr2' : r ^ (j + 1) ≤ 2 ^ (j + 1) := pow_le_pow_left₀ hr0.le hr2.le _
        have h6 : (3 : ℝ) ^ cl l n (j + 1) ≤ 6 * 2 ^ j := by
          calc (3 : ℝ) ^ cl l n (j + 1) ≤ 3 * r ^ (j + 1) := h3c
            _ ≤ 3 * 2 ^ (j + 1) := by gcongr
            _ = 6 * 2 ^ j := by ring
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) n]
      calc ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) * (3 ^ n / 6)
          ≤ ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) * ((2 : ℝ) ^ j * (3 : ℝ) ^ (n - cl l n (j + 1))) :=
            mul_le_mul_of_nonneg_left hge (Nat.cast_nonneg _)
        _ = _ := by ring
    calc (n : ℝ) * 3 ^ n / 6 = ∑ j ∈ Finset.range l, ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) * (3 ^ n / 6) := by
          rw [← Finset.sum_mul, sum_jumps, cl_l hl]; ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have hden : (0 : ℝ) < n * 3 ^ n := by positivity
  rw [le_div_iff₀ hden]
  linarith

theorem remark1_thm : remark1 := by
  intro l hl2
  have hl : 0 < l := by omega
  set n := nOf l with hndef
  have hn1 := nOf_pos hl2
  have hnl : n ≤ l := nOf_le l
  have h3 := three_pow_lt_of_le_nOf hl (le_refl n)
  have hr0 := rr_pos l n
  have hr2 := rr_lt_two hl h3
  have h3R : (2 : ℝ) ^ l < 3 ^ (n + 1) := by exact_mod_cast (nOf_spec_thm l hl).2
  set r := rr l n with hr
  have hden : (0 : ℝ) < n * 3 ^ n := by positivity
  refine ⟨le_trans (by norm_num) (remark1_lower6_thm l hl2), ?_⟩
  set v : ℝ := 2 / r with hv
  have hv1 : 1 ≤ v := by rw [hv, le_div_iff₀ hr0]; linarith
  have hvl : v ^ l = (2 : ℝ) ^ l / 3 ^ n := by rw [hv, div_pow, rr_pow_l n hl]
  set c : ℕ → ℝ := fun j => ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) with hc
  have hup : (M l n : ℝ) ≤ 3 ^ n / 3 * ∑ j ∈ Finset.range l, c j * v ^ j := by
    rw [M_range_real hl hnl, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have hcl : cl l n (j + 1) ≤ n := (cl_mono l n (by omega : j + 1 ≤ l)).trans (cl_l hl).le
    have htn := wt_toNat hl (by omega : n ≤ l) j
    cases hwj : wt l n j
    · rw [hwj, Bool.toNat_false] at htn
      have h0 : ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) = 0 := by rw [← htn]; simp
      have : c j = 0 := by simp only [hc]; exact h0
      rw [h0, this]
      simp
    · rw [hwj, Bool.toNat_true] at htn
      have hc1 : c j = 1 := by simp only [hc]; rw [← htn]; simp
      have hjump : cl l n (j + 1) = cl l n j + 1 := by
        have := cl_mono l n (Nat.le_succ j)
        omega
      have h3c : 3 * r ^ j ≤ (3 : ℝ) ^ (cl l n (j + 1)) := by
        rw [rr_pow, hjump, pow_succ, ← Real.rpow_natCast]
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have := cl_ge l n j
        push_cast at this ⊢
        exact this
      have hcast : ((cl l n (j + 1) - cl l n j : ℕ) : ℝ) = 1 := by rw [← htn]; simp
      have hpos : 0 < r ^ j := pow_pos hr0 _
      have hpos3 : 0 < (3 : ℝ) ^ (cl l n (j + 1)) := by positivity
      have e : (2 : ℝ) ^ j * (3 : ℝ) ^ (n - cl l n (j + 1)) = 3 ^ n * 2 ^ j / 3 ^ cl l n (j + 1) := by
        rw [pow_sub₀ (3 : ℝ) (by norm_num) hcl]; field_simp
      rw [hcast, hc1, one_mul, one_mul, e, hv, div_pow, div_le_iff₀ hpos3]
      have : (3 : ℝ) ^ n / 3 * (2 ^ j / r ^ j) * 3 ^ cl l n (j + 1)
          = (2 ^ j * 3 ^ n) * (3 ^ cl l n (j + 1) / (3 * r ^ j)) := by field_simp
      rw [this]
      have hge1 : 1 ≤ (3 : ℝ) ^ cl l n (j + 1) / (3 * r ^ j) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      calc (3 : ℝ) ^ n * 2 ^ j = (2 ^ j * 3 ^ n) * 1 := by ring
        _ ≤ (2 ^ j * 3 ^ n) * (3 ^ cl l n (j + 1) / (3 * r ^ j)) :=
          mul_le_mul_of_nonneg_left hge1 (by positivity)
  have hvmono : ∀ k, v ^ k ≤ v ^ (k + 1) := fun k => pow_le_pow_right₀ hv1 (Nat.le_succ k)
  have hpre : ∀ k, k ≤ l → (k : ℝ) * ((n : ℝ) / l) ≤ ∑ j ∈ Finset.range k, c j := by
    intro k _
    simp only [hc]
    rw [sum_jumps]
    have := cl_ge l n k
    calc (k : ℝ) * ((n : ℝ) / l) = (k * n : ℝ) / l := by ring
      _ ≤ _ := this
  have htot : ∑ j ∈ Finset.range l, c j = l * ((n : ℝ) / l) := by
    simp only [hc]
    rw [sum_jumps, cl_l hl]
    have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
    field_simp
  have habel := abel_le l c (fun j => v ^ j) ((n : ℝ) / l) hvmono hpre htot
  have hpair := two_mul_geom_le v hv1 l
  have hvl1 : v ^ (l - 1) ≤ v ^ l := pow_le_pow_right₀ hv1 (Nat.sub_le l 1)
  have hx3 : v ^ l < 3 := by
    rw [hvl, div_lt_iff₀ (by positivity)]
    calc (2 : ℝ) ^ l < 3 ^ (n + 1) := h3R
      _ = 3 * 3 ^ n := by ring
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  rw [div_le_iff₀ hden]
  have hsum : ∑ j ∈ Finset.range l, v ^ j ≤ 2 * l := by nlinarith
  calc (M l n : ℝ) ≤ 3 ^ n / 3 * ∑ j ∈ Finset.range l, c j * v ^ j := hup
    _ ≤ 3 ^ n / 3 * ((n : ℝ) / l * ∑ j ∈ Finset.range l, v ^ j) := by gcongr
    _ ≤ 3 ^ n / 3 * ((n : ℝ) / l * (2 * l)) := by gcongr
    _ = 2 / 3 * (n * 3 ^ n) := by field_simp
    _ ≤ 7 / 10 * (n * 3 ^ n) := mul_le_mul_of_nonneg_right (by norm_num) hden.le

/-! ## The numerical example of §4.4: reduction to the finite check -/

lemma T_cast (k : ℤ) : collatzQ (k : ℚ) = ((T k : ℤ) : ℚ) := by
  unfold collatzQ T
  rw [Rat.num_intCast]
  by_cases h : k % 2 = 0
  · simp only [h, ↓reduceIte]
    have h2 : (2 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero h
    rw [Int.cast_div h2 (by norm_num)]
    push_cast
    ring
  · simp only [h, ↓reduceIte]
    have h2 : (2 : ℤ) ∣ 3 * k + 1 := by omega
    rw [Int.cast_div h2 (by norm_num)]
    push_cast
    ring

lemma T_iter_cast (i : ℕ) : ∀ k : ℤ, collatzQ^[i] (k : ℚ) = ((T^[i] k : ℤ) : ℚ) := by
  induction i with
  | zero => intro k; rfl
  | succ i ih => intro k; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T_cast, ih]

lemma T_pos (k : ℤ) (hk : 0 < k) : 0 < T k := by
  unfold T
  split_ifs <;> omega

lemma T_iter_pos (i : ℕ) : ∀ k : ℤ, 0 < k → 0 < T^[i] k := by
  induction i with
  | zero => intro k hk; exact hk
  | succ i ih => intro k hk; rw [Function.iterate_succ_apply]; exact ih _ (T_pos k hk)

theorem example44_reduction_thm : example44_reduction := by
  intro hcheck hver x₀ hx1 hper hne1
  have hp : 0 < Function.minimalPeriod T (x₀ : ℤ) := Function.minimalPeriod_pos_of_mem_periodicPts hper
  by_contra hlt
  push Not at hlt
  have hTp : T^[Function.minimalPeriod T (x₀ : ℤ)] (x₀ : ℤ) = x₀ := Function.iterate_minimalPeriod
  have hQp : collatzQ^[Function.minimalPeriod T (x₀ : ℤ)] (((x₀ : ℤ) : ℚ)) = ((x₀ : ℤ) : ℚ) := by
    rw [T_iter_cast, hTp]
  have hperQ : ((x₀ : ℤ) : ℚ) ∈ Function.periodicPts collatzQ := ⟨_, hp, hQp⟩
  have hden : Odd (((x₀ : ℤ) : ℚ)).den := by simp
  have hx0pos : (0 : ℤ) < x₀ := by exact_mod_cast hx1
  have hposC : ∀ y ∈ cycle ((x₀ : ℤ) : ℚ), 0 < y := by
    rintro _ ⟨i, rfl⟩
    show 0 < collatzQ^[i] (((x₀ : ℤ) : ℚ))
    rw [T_iter_cast]
    exact_mod_cast T_iter_pos i _ hx0pos
  obtain ⟨m, hm⟩ := cycle_min_exists _ hperQ
  have hcore := thm4_core_thm _ hden hperQ hposC m hm
  rw [cycle_ncard _ hperQ] at hcore
  have hP'le : Function.minimalPeriod collatzQ (((x₀ : ℤ) : ℚ)) ≤ Function.minimalPeriod T (x₀ : ℤ) :=
    Function.IsPeriodicPt.minimalPeriod_le hp hQp
  have hP'pos := Function.minimalPeriod_pos_of_mem_periodicPts hperQ
  have hQ := hcheck _ hP'pos (by omega)
  obtain ⟨i, hi⟩ := hm.1
  have hmB : (212366032807211 : ℚ) < m := by
    rw [← hi]
    show (212366032807211 : ℚ) < collatzQ^[i] (((x₀ : ℤ) : ℚ))
    rw [T_iter_cast]
    have hz : 0 < T^[i] (x₀ : ℤ) := T_iter_pos i _ hx0pos
    by_contra hle
    push Not at hle
    have hzle : T^[i] (x₀ : ℤ) ≤ 212366032807211 := by exact_mod_cast hle
    obtain ⟨k, hk⟩ := hver (T^[i] (x₀ : ℤ)).toNat (by omega) (by omega)
    rw [Int.toNat_of_nonneg hz.le] at hk
    exact hne1 (k + i) (by rw [Function.iterate_add_apply, hk])
  linarith

/-! ## Proposition 2: tools on `n(l)` and `⌈jn/l⌉` -/

/-- `m = 2n − l` as a natural number. -/
noncomputable def mN (l : ℕ) : ℕ := 2 * nOf l - l

lemma nOf_eq {l n : ℕ} (hl : 0 < l) (h1 : 3 ^ n < 2 ^ l) (h2 : 2 ^ l < 3 ^ (n + 1)) : nOf l = n := by
  obtain ⟨g1, g2⟩ := nOf_spec_thm l hl
  have a : n < nOf l + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (h1.trans g2)
  have b : nOf l < n + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (g1.trans h2)
  omega

lemma three_pow_6309 : 3 ^ 6309 < 2 ^ 10000 := by decide +kernel

/-- `log₃ 2 > 0.6309`, in the form `10000 (n(l) + 1) > 6309 l`. -/
lemma nOf_ge (l : ℕ) (hl : 0 < l) : 6309 * l < 10000 * (nOf l + 1) := by
  by_contra h
  push Not at h
  have g2 := (nOf_spec_thm l hl).2
  have e1 : 2 ^ (10000 * l) < 3 ^ (10000 * (nOf l + 1)) := by
    rw [pow_mul', pow_mul']
    exact Nat.pow_lt_pow_left g2 (by norm_num)
  have e2 : 3 ^ (10000 * (nOf l + 1)) ≤ 3 ^ (6309 * l) := Nat.pow_le_pow_right (by norm_num) h
  have e3 : 3 ^ (6309 * l) < 2 ^ (10000 * l) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left three_pow_6309 (by omega)
  omega

lemma three_nOf_lt (l : ℕ) (hl : 0 < l) : 3 * nOf l < 2 * l := by
  by_contra h
  push Not at h
  have g1 := (nOf_spec_thm l hl).1
  have e1 : 3 ^ (2 * l) ≤ 3 ^ (3 * nOf l) := Nat.pow_le_pow_right (by norm_num) h
  have e2 : 3 ^ (3 * nOf l) < 2 ^ (3 * l) := by
    rw [pow_mul', pow_mul']
    exact Nat.pow_lt_pow_left g1 (by norm_num)
  have e3 : 2 ^ (3 * l) < 3 ^ (2 * l) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  omega

lemma l_lt_two_nOf (l : ℕ) (hl : 7 ≤ l) : l < 2 * nOf l := by
  have := nOf_ge l (by omega)
  omega

lemma five_nOf (l : ℕ) (hl : 23 ≤ l) : 3 * l ≤ 5 * nOf l := by
  have := nOf_ge l (by omega)
  rcases Nat.lt_or_ge l 33 with h | h
  · interval_cases l <;> omega
  · omega

lemma le_cl_mul {l n : ℕ} (hl : 0 < l) (j : ℕ) : j * n ≤ cl l n j * l := (cl_le_iff hl).mp le_rfl

lemma cl_mul_lt {l n : ℕ} (hl : 0 < l) (j : ℕ) : cl l n j * l < j * n + l := by
  rcases Nat.eq_zero_or_pos (cl l n j) with h | h
  · rw [h]
    omega
  · have h' : ¬ cl l n j ≤ cl l n j - 1 := by omega
    rw [cl_le_iff hl] at h'
    push Not at h'
    have e : cl l n j * l = (cl l n j - 1) * l + l := by
      conv_lhs => rw [show cl l n j = (cl l n j - 1) + 1 by omega]
      ring
    rw [e]
    omega

lemma wt_true_iff {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (i : ℕ) :
    wt l n i = true ↔ cl l n (i + 1) = cl l n i + 1 := by
  have h1 := cl_succ_le hl hn i
  have h2 := cl_mono l n (show i ≤ i + 1 by omega)
  unfold wt
  constructor
  · intro h; have := of_decide_eq_true h; omega
  · intro h; exact decide_eq_true (by omega)

lemma wt_false_iff {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (i : ℕ) :
    wt l n i = false ↔ cl l n (i + 1) = cl l n i := by
  have h1 := cl_succ_le hl hn i
  have h2 := cl_mono l n (show i ≤ i + 1 by omega)
  unfold wt
  constructor
  · intro h; have := of_decide_eq_false h; omega
  · intro h; exact decide_eq_false (by omega)

/-! ## Proposition 2: the decomposition of `s̃` into `Z = 110` and `A = 11010` -/

/-- The block of letter `b`: `A` for `true`, `Z` for `false`. -/
def blk (b : Bool) : List Bool := if b then blockA else blockZ

lemma stilde_getElem? {l n i : ℕ} (hi : i < l) : (stilde l n)[i]? = some (wt l n i) := by
  simp [stilde, wt, hi]

lemma infix_letters {l n : ℕ} {u : List Bool} (h : u <:+: stilde l n) :
    ∃ i, i + u.length ≤ l ∧ ∀ k, k < u.length → some (wt l n (i + k)) = u[k]? := by
  obtain ⟨s, t, hst⟩ := h
  have hlen : s.length + u.length + t.length = l := by
    have := congrArg List.length hst
    simp only [List.length_append, stilde_length] at this
    omega
  refine ⟨s.length, by omega, fun k hk => ?_⟩
  rw [← stilde_getElem? (by omega), ← hst, List.getElem?_append_left (by simp; omega),
    List.getElem?_append_right (by omega)]
  simp

lemma no_ff {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (h2 : l < 2 * n) : ¬ [false, false] <:+: stilde l n := by
  intro h
  obtain ⟨i, -, hk⟩ := infix_letters h
  have w0 := hk 0 (by simp)
  have w1 := hk 1 (by simp)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, add_zero] at w0 w1
  rw [wt_false_iff hl hn] at w0 w1
  have a := le_cl_mul (n := n) hl (i + 1 + 1)
  have b := cl_mul_lt (n := n) hl i
  rw [w1, w0] at a
  nlinarith

lemma no_ttt {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (h3 : 3 * n < 2 * l) :
    ¬ [true, true, true] <:+: stilde l n := by
  intro h
  obtain ⟨i, -, hk⟩ := infix_letters h
  have w0 := hk 0 (by simp)
  have w1 := hk 1 (by simp)
  have w2 := hk 2 (by simp)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, add_zero] at w0 w1 w2
  rw [wt_true_iff hl hn] at w0 w1 w2
  have a := cl_add_le l n i 3
  have b : cl l n 3 ≤ 2 := by rw [cl_le_iff hl]; omega
  rw [show i + 3 = i + 2 + 1 by ring, w2, show i + 2 = i + 1 + 1 by ring, w1, w0] at a
  omega

lemma no_ftftf {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (h5 : 3 * l ≤ 5 * n) :
    ¬ [false, true, false, true, false] <:+: stilde l n := by
  intro h
  obtain ⟨i, -, hk⟩ := infix_letters h
  have w0 := hk 0 (by simp)
  have w1 := hk 1 (by simp)
  have w2 := hk 2 (by simp)
  have w3 := hk 3 (by simp)
  have w4 := hk 4 (by simp)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, add_zero] at w0 w1 w2 w3 w4
  rw [wt_false_iff hl hn] at w0 w2 w4
  rw [wt_true_iff hl hn] at w1 w3
  have a := le_cl_mul (n := n) hl (i + 4 + 1)
  have b := cl_mul_lt (n := n) hl i
  rw [w4, show i + 4 = i + 3 + 1 by ring, w3, show i + 3 = i + 2 + 1 by ring, w2,
    show i + 2 = i + 1 + 1 by ring, w1, w0] at a
  nlinarith

lemma stilde_prefix11 {l n : ℕ} (hl : 2 ≤ l) (hn1 : 1 ≤ n) (hn : n ≤ l) (h2 : l < 2 * n) :
    [true, true] <+: stilde l n := by
  have hl0 : 0 < l := by omega
  rw [List.prefix_iff_eq_take]
  have e0 : wt l n 0 = true := by
    rw [wt_true_iff hl0 hn, cl_zero, zero_add]
    have : ¬ cl l n 1 ≤ 0 := by rw [cl_le_iff hl0]; omega
    have : cl l n 1 ≤ 1 := by rw [cl_le_iff hl0]; omega
    omega
  have e1 : wt l n 1 = true := by
    rw [wt_true_iff hl0 hn, show (1 : ℕ) + 1 = 2 by rfl]
    have : ¬ cl l n 2 ≤ 1 := by rw [cl_le_iff hl0]; omega
    have : cl l n 1 ≤ 1 := by rw [cl_le_iff hl0]; omega
    have : 1 ≤ cl l n 1 := by
      by_contra hc; push Not at hc
      have : cl l n 1 ≤ 0 := by omega
      rw [cl_le_iff hl0] at this; omega
    have := cl_succ_le hl0 hn 1
    rw [show (1 : ℕ) + 1 = 2 by rfl] at this
    omega
  simp only [List.length_cons, List.length_nil, stilde]
  rw [← List.map_take, List.take_range, Nat.min_eq_left hl]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.singleton_append]
  exact (congrArg₂ (fun a b => [a, b]) e0 e1).symm

lemma stilde_last {l n : ℕ} (hl : 0 < l) (hn1 : 1 ≤ n) (hn : n < l) : (stilde l n).getLast? = some false := by
  have hwl : wt l n (l - 1) = false := by
    rw [wt_false_iff hl hn.le, show l - 1 + 1 = l by omega, cl_l hl]
    have hle : cl l n (l - 1) ≤ n := (cl_mono l n (Nat.sub_le l 1)).trans (cl_l hl).le
    have hge : ¬ cl l n (l - 1) ≤ n - 1 := by
      rw [cl_le_iff hl]
      intro h
      have e1 : (l - 1) * n + n = l * n := by
        conv_rhs => rw [show l = (l - 1) + 1 by omega]
        ring
      have e2 : (n - 1) * l + l = n * l := by
        conv_rhs => rw [show n = (n - 1) + 1 by omega]
        ring
      nlinarith
    omega
  have hr : List.range l = List.range (l - 1) ++ [l - 1] := by
    conv_lhs => rw [show l = l - 1 + 1 by omega]
    exact List.range_succ
  have e : stilde l n = (List.range (l - 1)).map (wt l n) ++ [wt l n (l - 1)] := by
    simp only [stilde]
    rw [hr, List.map_append]
    rfl
  rw [e, hwl]
  simp

/-- A word without `00`, `111`, `01010`, starting with `11` and ending with `0`, is a concatenation of `Z` and `A`. -/
lemma parse_blocks : ∀ (k : ℕ) (w : List Bool), w.length ≤ k →
    ¬ [false, false] <:+: w → ¬ [true, true, true] <:+: w → ¬ [false, true, false, true, false] <:+: w →
    (w = [] ∨ ([true, true] <+: w ∧ w.getLast? = some false)) →
    ∃ bs : List Bool, w = bs.flatMap blk := by
  intro k
  induction k with
  | zero =>
    intro w hw _ _ _ _
    exact ⟨[], by simpa using hw⟩
  | succ k ih =>
    intro w hw h00 h111 h01010 hshape
    rcases hshape with rfl | ⟨hpre, hlast⟩
    · exact ⟨[], rfl⟩
    obtain ⟨w2, rfl⟩ : ∃ w2, w = true :: true :: w2 := by
      obtain ⟨t, ht⟩ := hpre
      exact ⟨t, ht.symm⟩
    rcases w2 with _ | ⟨b, w3⟩
    · simp at hlast
    cases b
    swap
    · exact absurd ⟨[], w3, rfl⟩ h111
    rcases w3 with _ | ⟨c, w4⟩
    · exact ⟨[false], rfl⟩
    cases c
    · exact absurd ⟨[true, true], w4, rfl⟩ h00
    rcases w4 with _ | ⟨d, w5⟩
    · simp at hlast
    cases d
    swap
    · obtain ⟨bs, hbs⟩ := ih (true :: true :: w5) (by simp at hw ⊢; omega)
        (fun h => h00 (h.trans (List.suffix_append [true, true, false] _).isInfix))
        (fun h => h111 (h.trans (List.suffix_append [true, true, false] _).isInfix))
        (fun h => h01010 (h.trans (List.suffix_append [true, true, false] _).isInfix))
        (Or.inr ⟨⟨w5, rfl⟩, by simpa using hlast⟩)
      exact ⟨false :: bs, by rw [List.flatMap_cons, ← hbs]; rfl⟩
    rcases w5 with _ | ⟨e, w6⟩
    · exact ⟨[true], rfl⟩
    cases e
    · exact absurd ⟨[true, true, false, true], w6, rfl⟩ h00
    rcases w6 with _ | ⟨f, w7⟩
    · simp at hlast
    cases f
    · exact absurd ⟨[true, true], w7, rfl⟩ h01010
    obtain ⟨bs, hbs⟩ := ih (true :: true :: w7) (by simp at hw ⊢; omega)
      (fun h => h00 (h.trans (List.suffix_append [true, true, false, true, false] _).isInfix))
      (fun h => h111 (h.trans (List.suffix_append [true, true, false, true, false] _).isInfix))
      (fun h => h01010 (h.trans (List.suffix_append [true, true, false, true, false] _).isInfix))
      (Or.inr ⟨⟨w7, rfl⟩, by simpa using hlast⟩)
    exact ⟨true :: bs, by rw [List.flatMap_cons, ← hbs]; rfl⟩

lemma decomp {l n : ℕ} (hl : 2 ≤ l) (hn1 : 1 ≤ n) (hn : n < l) (h2 : l < 2 * n) (h3 : 3 * n < 2 * l)
    (h5 : 3 * l ≤ 5 * n) : ∃ bs : List Bool, stilde l n = bs.flatMap blk := by
  have hl0 : 0 < l := by omega
  exact parse_blocks _ _ le_rfl (no_ff hl0 hn.le h2) (no_ttt hl0 hn.le h3) (no_ftftf hl0 hn.le h5)
    (Or.inr ⟨stilde_prefix11 hl hn1 hn.le h2, stilde_last hl0 hn1 hn⟩)

theorem blocks23_thm : blocks23 := by
  intro l hl
  have hl0 : 0 < l := by omega
  exact decomp (by omega) (by have := l_lt_two_nOf l (by omega); omega) (by have := three_nOf_lt l hl0; omega)
    (l_lt_two_nOf l (by omega)) (three_nOf_lt l hl0) (five_nOf l hl)

theorem blocks160_thm : blocks160 := fun l hl => blocks23_thm l (by omega)

/-! ## Proposition 2: the block sum (8) and the estimate (10) -/

/-- Length, number of `1`, `χ` and weight of the blocks `A` (`true`) and `Z` (`false`). -/
def lenB (b : Bool) : ℕ := if b then 5 else 3
def cntB (b : Bool) : ℕ := if b then 3 else 2
noncomputable def chiB (b : Bool) : ℝ := if b then 23 / 27 else 5 / 9
noncomputable def rhoB (b : Bool) : ℝ := if b then 32 / 27 else 8 / 9

lemma blk_length (b : Bool) : (blk b).length = lenB b := by cases b <;> rfl
lemma blk_count (b : Bool) : (blk b).count true = cntB b := by cases b <;> rfl
lemma phi_blk (b : Bool) : phi (blk b) = if b then 23 else 5 := by cases b <;> rfl
lemma cnt_len (b : Bool) : 2 * cntB b = lenB b + 1 := by cases b <;> rfl
lemma chiB_eq (b : Bool) : chiB b = (6 * (cntB b : ℝ) + lenB b) / 27 := by
  cases b <;> norm_num [chiB, cntB, lenB]
lemma rhoB_eq (b : Bool) : rhoB b = (2 : ℝ) ^ lenB b / 3 ^ cntB b := by
  cases b <;> norm_num [rhoB, cntB, lenB]
lemma chiB_nonneg (b : Bool) : 0 ≤ chiB b := by cases b <;> norm_num [chiB]

/-- (8): `ϕ(W)/3^{n(W)} = Σ_k χ(a_k)·Π_{i<k} ρ(a_i)` for `W = a_0 ⋯ a_{m−1}`. -/
lemma phi_flatMap (bs : List Bool) :
    (phi (bs.flatMap blk) : ℝ) / 3 ^ ((bs.flatMap blk).count true)
      = ∑ k ∈ Finset.range bs.length, chiB (bs.getD k false) * ∏ i ∈ Finset.range k, rhoB (bs.getD i false) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.flatMap_cons, eq4_thm, List.count_append, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Finset.prod_range_succ', Finset.prod_range_zero, mul_one]
    have hrw : ∑ k ∈ Finset.range bs.length,
        chiB (bs.getD k false) * ((∏ i ∈ Finset.range k, rhoB (bs.getD i false)) * rhoB b)
        = rhoB b * ∑ k ∈ Finset.range bs.length,
          chiB (bs.getD k false) * ∏ i ∈ Finset.range k, rhoB (bs.getD i false) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hrw, ← ih, blk_count, blk_length, phi_blk]
    push_cast
    cases b <;> simp only [chiB, rhoB, cntB, lenB, ↓reduceIte, Bool.false_eq_true] <;> field_simp <;> ring

lemma prod_rho (bs : List Bool) (k : ℕ) :
    ∏ i ∈ Finset.range k, rhoB (bs.getD i false)
      = (2 : ℝ) ^ (∑ i ∈ Finset.range k, lenB (bs.getD i false))
        / 3 ^ (∑ i ∈ Finset.range k, cntB (bs.getD i false)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, rhoB_eq, Finset.sum_range_succ, Finset.sum_range_succ, pow_add, pow_add]
    field_simp

lemma take_flatMap_length (bs : List Bool) (k : ℕ) (hk : k ≤ bs.length) :
    ((bs.take k).flatMap blk).length = ∑ i ∈ Finset.range k, lenB (bs.getD i false) := by
  induction bs generalizing k with
  | nil => simp at hk; subst hk; simp
  | cons b bs ih =>
    rcases k with _ | k
    · simp
    · rw [List.take_succ_cons, List.flatMap_cons, List.length_append, blk_length, ih k (by simp at hk; omega),
        Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

lemma take_flatMap_count (bs : List Bool) (k : ℕ) (hk : k ≤ bs.length) :
    ((bs.take k).flatMap blk).count true = ∑ i ∈ Finset.range k, cntB (bs.getD i false) := by
  induction bs generalizing k with
  | nil => simp at hk; subst hk; simp
  | cons b bs ih =>
    rcases k with _ | k
    · simp
    · rw [List.take_succ_cons, List.flatMap_cons, List.count_append, blk_count, ih k (by simp at hk; omega),
        Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

/-- Abel inequality, suffix form: with non-decreasing non-negative weights, suffix domination is enough. -/
lemma abel_suffix (L : ℕ) (c d w : ℕ → ℝ) (hw : ∀ k, w k ≤ w (k + 1)) (hw0 : 0 ≤ w 0)
    (hsuf : ∀ j, j ≤ L → ∑ k ∈ Finset.Ico j L, c k ≤ ∑ k ∈ Finset.Ico j L, d k) :
    ∑ k ∈ Finset.range L, c k * w k ≤ ∑ k ∈ Finset.range L, d k * w k := by
  have key : ∀ t, t ≤ L → (∑ k ∈ Finset.Ico (L - t) L, (d k - c k)) * w (L - t)
      ≤ ∑ k ∈ Finset.Ico (L - t) L, (d k - c k) * w k := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have hj : L - (t + 1) < L := by omega
      have e : L - (t + 1) + 1 = L - t := by omega
      rw [Finset.sum_eq_sum_Ico_succ_bot hj, Finset.sum_eq_sum_Ico_succ_bot hj, e]
      have hS : 0 ≤ ∑ k ∈ Finset.Ico (L - t) L, (d k - c k) := by
        rw [Finset.sum_sub_distrib]
        linarith [hsuf (L - t) (by omega)]
      have hmono : w (L - (t + 1)) ≤ w (L - t) := by rw [← e]; exact hw _
      have ih' := ih (by omega)
      nlinarith [mul_le_mul_of_nonneg_left hmono hS]
  have h := key L le_rfl
  rw [Nat.sub_self, ← Finset.range_eq_Ico] at h
  have h0 : 0 ≤ ∑ k ∈ Finset.range L, (d k - c k) := by
    rw [Finset.range_eq_Ico, Finset.sum_sub_distrib]
    linarith [hsuf 0 (by omega)]
  have h1 : 0 ≤ ∑ k ∈ Finset.range L, (d k - c k) * w k := le_trans (mul_nonneg h0 hw0) h
  have hs : ∑ k ∈ Finset.range L, (d k - c k) * w k
      = ∑ k ∈ Finset.range L, d k * w k - ∑ k ∈ Finset.range L, c k * w k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linarith

/-- The structural half of Prop. 2: if `s̃(l,n)` is a concatenation of `A` and `Z`, then (10) and Lemma 3 give
the bound, for any `y ≥ 1` with `y^m = 2^l/3^n`, `m = 2n − l`. -/
theorem prop2_struct (l n : ℕ) (hl : 0 < l) (hn : n ≤ l) (hm : l < 2 * n) (h3 : 3 ^ n < 2 ^ l)
    (bs : List Bool) (hW : stilde l n = bs.flatMap blk) (y : ℝ) (hy1 : 1 ≤ y)
    (hym : y ^ (2 * n - l) = (2 : ℝ) ^ l / 3 ^ n) :
    (M l n : ℝ) / 3 ^ n ≤ (2 * n + 3 * l : ℝ) / (9 * ((2 * n - l : ℕ) : ℝ)) * y ^ (2 * n - l - 1)
      + (6 * n + l : ℝ) / (27 * ((2 * n - l : ℕ) : ℝ)) * ∑ k ∈ Finset.range (2 * n - l - 1), y ^ k := by
  set m := 2 * n - l with hmdef
  have hm1 : 1 ≤ m := by omega
  set Lf : ℕ → ℕ := fun k => ∑ i ∈ Finset.range k, lenB (bs.getD i false) with hLf
  set Nf : ℕ → ℕ := fun k => ∑ i ∈ Finset.range k, cntB (bs.getD i false) with hNf
  have hkey : ∀ k, 2 * Nf k = Lf k + k := by
    intro k
    simp only [hLf, hNf]
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih, cnt_len]; ring
  have hlenW : Lf bs.length = l := by
    have := congrArg List.length hW
    rw [stilde_length, ← List.take_length (l := bs), take_flatMap_length bs bs.length le_rfl] at this
    exact this.symm
  have hcntW : Nf bs.length = n := by
    have h := stilde_count hl hn
    rw [hW, ← List.take_length (l := bs), take_flatMap_count bs bs.length le_rfl] at h
    exact h
  have hbslen : bs.length = m := by have := hkey bs.length; omega
  have hpre : ∀ k, k ≤ bs.length → Nf k = cl l n (Lf k) := by
    intro k hk
    have hLk : Lf k ≤ l := by
      rw [← hlenW]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono hk)
    have hpw : (stilde l n).take (Lf k) = (bs.take k).flatMap blk := by
      rw [hW]
      conv_lhs => rw [← List.take_append_drop k bs, List.flatMap_append]
      rw [show Lf k = ((bs.take k).flatMap blk).length from (take_flatMap_length bs k hk).symm, List.take_left]
    rw [← stilde_prefix hl hn (Lf k) hLk, hpw, take_flatMap_count bs k hk]
  have hM : (M l n : ℝ) / 3 ^ n
      = ∑ k ∈ Finset.range m, chiB (bs.getD k false) * ((2 : ℝ) ^ (Lf k) / 3 ^ (Nf k)) := by
    have hc : (bs.flatMap blk).count true = n := by rw [← hW]; exact stilde_count hl hn
    rw [M_eq_phi_stilde hl hn, hW, ← hbslen]
    conv_lhs => rw [← hc]
    rw [phi_flatMap]
    exact Finset.sum_congr rfl fun k _ => by rw [prod_rho]
  have ht : ∀ k, k ≤ m → (2 : ℝ) ^ (Lf k) / 3 ^ (Nf k) ≤ y ^ k := by
    intro k hk
    have hNk := hpre k (by omega)
    have hA : Lf k * n ≤ Nf k * l := by rw [hNk]; exact le_cl_mul hl _
    have hk2 := hkey k
    have hmZ : (m : ℤ) = 2 * n - l := by rw [hmdef]; push_cast [show l ≤ 2 * n by omega]; ring
    have hk2' : (2 : ℤ) * Nf k = Lf k + k := by exact_mod_cast hkey k
    have e1 : l * k = Lf k * m + 2 * (Nf k * l - Lf k * n) := by
      zify [hA]
      linear_combination (-(l : ℤ)) * hk2' + (-(Lf k : ℤ)) * hmZ
    have e2 : n * k = Nf k * m + (Nf k * l - Lf k * n) := by
      zify [hA]
      linear_combination (-(n : ℤ)) * hk2' + (-(Nf k : ℤ)) * hmZ
    have hnat : 2 ^ (Lf k * m) * 3 ^ (n * k) ≤ 2 ^ (l * k) * 3 ^ (Nf k * m) := by
      rw [e1, e2, pow_add, pow_add, pow_mul 2 2]
      have : 3 ^ (Nf k * l - Lf k * n) ≤ (2 ^ 2) ^ (Nf k * l - Lf k * n) := Nat.pow_le_pow_left (by norm_num) _
      calc 2 ^ (Lf k * m) * (3 ^ (Nf k * m) * 3 ^ (Nf k * l - Lf k * n))
          ≤ 2 ^ (Lf k * m) * (3 ^ (Nf k * m) * (2 ^ 2) ^ (Nf k * l - Lf k * n)) := by gcongr
        _ = 2 ^ (Lf k * m) * (2 ^ 2) ^ (Nf k * l - Lf k * n) * 3 ^ (Nf k * m) := by ring
    have hreal : ((2 : ℝ) ^ (Lf k) / 3 ^ (Nf k)) ^ m ≤ (y ^ k) ^ m := by
      rw [← pow_mul, mul_comm k m, pow_mul, hym, div_pow, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
        div_le_div_iff₀ (by positivity) (by positivity)]
      exact_mod_cast hnat
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp hreal
  have hS1 : ∑ k ∈ Finset.range m, chiB (bs.getD k false) * ((2 : ℝ) ^ (Lf k) / 3 ^ (Nf k))
      ≤ ∑ k ∈ Finset.range m, chiB (bs.getD k false) * y ^ k :=
    Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_left (ht k (Finset.mem_range.mp hk).le) (chiB_nonneg _)
  set a1 : ℝ := (2 * n + 3 * l : ℝ) / (9 * (m : ℝ)) with ha1
  set a2 : ℝ := (6 * n + l : ℝ) / (27 * (m : ℝ)) with ha2
  set d : ℕ → ℝ := fun k => if k + 1 = m then a1 else a2 with hd
  have hmR : (m : ℝ) = 2 * n - l := by rw [hmdef]; push_cast [show l ≤ 2 * n by omega]; ring
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hchi_sum : ∀ K, ∑ k ∈ Finset.range K, chiB (bs.getD k false) = (6 * (Nf K : ℝ) + Lf K) / 27 := by
    intro K
    simp only [hNf, hLf, chiB_eq]
    rw [← Finset.sum_div]
    push_cast
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hsuf : ∀ j, j ≤ m →
      ∑ k ∈ Finset.Ico j m, chiB (bs.getD k false) ≤ ∑ k ∈ Finset.Ico j m, d k := by
    intro j hj
    rcases hj.lt_or_eq with hj | rfl
    · have hlenW' : Lf m = l := hbslen ▸ hlenW
      have hcntW' : Nf m = n := hbslen ▸ hcntW
      rw [Finset.sum_Ico_eq_sub _ hj.le, hchi_sum, hchi_sum, hlenW', hcntW']
      have hdsum : ∑ k ∈ Finset.Ico j m, d k = a1 + ((m - 1 - j : ℕ) : ℝ) * a2 := by
        rw [show m = (m - 1) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
        have h1 : ∀ k ∈ Finset.Ico j (m - 1), d k = a2 := by
          intro k hk
          have := (Finset.mem_Ico.mp hk).2
          simp only [hd]
          rw [if_neg (by omega)]
        rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        simp only [hd, show m - 1 + 1 = m by omega, ↓reduceIte]
        ring
      rw [hdsum]
      have hNj := hpre j (by omega)
      have hB : Nf j * l < Lf j * n + l := by rw [hNj]; exact cl_mul_lt hl _
      have hBR : (Nf j : ℝ) * l ≤ Lf j * n + l := by exact_mod_cast hB.le
      have hjR : (j : ℝ) = 2 * Nf j - Lf j := by
        have := hkey j
        have : ((2 * Nf j : ℕ) : ℝ) = ((Lf j + j : ℕ) : ℝ) := by rw [this]
        push_cast at this
        linarith
      have hcast : ((m - 1 - j : ℕ) : ℝ) = m - 1 - j := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        simp
      rw [hcast, ha1, ha2]
      have hdiff : (2 * n + 3 * l : ℝ) / (9 * m) + (m - 1 - j) * ((6 * n + l) / (27 * m))
          - (6 * (n : ℝ) + l - (6 * (Nf j : ℝ) + Lf j)) / 27
          = 8 * ((Lf j : ℝ) * n + l - Nf j * l) / (27 * m) := by
        rw [hjR]
        field_simp
        rw [hmR]
        ring
      have hnonneg : 0 ≤ 8 * ((Lf j : ℝ) * n + l - Nf j * l) / (27 * m) := by
        apply div_nonneg _ (by positivity)
        linarith
      have hnum : (6 * (n : ℝ) + l - (6 * (Nf j : ℝ) + Lf j)) / 27
          = (6 * (n : ℝ) + l) / 27 - (6 * (Nf j : ℝ) + Lf j) / 27 := by ring
      rw [hnum] at hdiff
      linarith
    · simp
  have hab := abel_suffix m (fun k => chiB (bs.getD k false)) d (fun k => y ^ k)
    (fun k => pow_le_pow_right₀ hy1 (Nat.le_succ k)) (by simp) hsuf
  have hdy : ∑ k ∈ Finset.range m, d k * y ^ k = a1 * y ^ (m - 1) + a2 * ∑ k ∈ Finset.range (m - 1), y ^ k := by
    rw [show m = (m - 1) + 1 by omega, Finset.sum_range_succ]
    simp only [hd, show m - 1 + 1 = m by omega, ↓reduceIte]
    rw [Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by
      rw [if_neg (by have := Finset.mem_range.mp hk; omega)]
  rw [hM]
  calc _ ≤ ∑ k ∈ Finset.range m, chiB (bs.getD k false) * y ^ k := hS1
    _ ≤ ∑ k ∈ Finset.range m, d k * y ^ k := hab
    _ = _ := hdy

/-! ## Proposition 2: the finitely many small `l` (`7 ≤ l ≤ 22`), by kernel computation -/

lemma cl_eq_cdiv {l n : ℕ} (hl : 0 < l) (j : ℕ) : cl l n j = (j * n + l - 1) / l := by
  apply le_antisymm
  · rw [cl_le_iff hl]
    have h := Nat.lt_div_mul_add (a := j * n + l - 1) hl
    omega
  · have h := le_cl_mul (n := n) hl j
    have : (j * n + l - 1) / l < cl l n j + 1 := by
      rw [Nat.div_lt_iff_lt_mul hl]
      have : (cl l n j + 1) * l = cl l n j * l + l := by ring
      omega
    omega

/-- A computable copy of `s̃` (integer ceiling division). -/
def stildeC (l n : ℕ) : List Bool :=
  (List.range l).map fun i => decide ((i * n + l - 1) / l < ((i + 1) * n + l - 1) / l)

lemma stilde_eq_C {l n : ℕ} (hl : 0 < l) : stilde l n = stildeC l n := by
  simp only [stilde, stildeC, cl_eq_cdiv hl]

lemma small_case (l n0 M0 : ℕ) (hl : 0 < l) (h1 : 3 ^ n0 < 2 ^ l) (h2 : 2 ^ l < 3 ^ (n0 + 1)) (hn0 : n0 ≤ l)
    (hM : phi (stildeC l n0) = M0)
    (hineq : (M0 : ℝ) / 3 ^ n0 ≤ (2 * n0 + 3 * l : ℝ) / (9 * ((2 * n0 - l : ℕ) : ℝ)) * 1
      + (6 * n0 + l : ℝ) / (27 * ((2 * n0 - l : ℕ) : ℝ)) * ((2 * n0 - l - 1 : ℕ) : ℝ)) :
    (M l (nOf l) : ℝ) / 3 ^ nOf l ≤ (2 * nOf l + 3 * l : ℝ) / (9 * ((2 * nOf l - l : ℕ) : ℝ)) * 1
      + (6 * nOf l + l : ℝ) / (27 * ((2 * nOf l - l : ℕ) : ℝ)) * ((2 * nOf l - l - 1 : ℕ) : ℝ) := by
  rw [nOf_eq hl h1 h2, M_eq_phi_stilde hl hn0, stilde_eq_C hl, hM]
  exact hineq

theorem prop2_thm : prop2 := by
  intro l hl6
  have hl0 : 0 < l := by omega
  have h2n : l < 2 * nOf l := l_lt_two_nOf l (by omega)
  have hnl : nOf l ≤ l := nOf_le l
  have h3 : 3 ^ nOf l < 2 ^ l := (nOf_spec_thm l hl0).1
  have hm1 : 1 ≤ 2 * nOf l - l := by omega
  have hmR : mR l = ((2 * nOf l - l : ℕ) : ℝ) := by
    unfold mR
    push_cast [h2n.le]
    ring
  have hmpos : (0 : ℝ) < ((2 * nOf l - l : ℕ) : ℝ) := by exact_mod_cast hm1
  refine ⟨hmR ▸ hmpos, ?_⟩
  have hx1 : 1 < xP l := by
    unfold xP
    rw [one_lt_div (by positivity)]
    exact_mod_cast h3
  set m := 2 * nOf l - l with hmdef
  set y := xP l ^ (1 / mR l) with hy
  have hy1 : 1 < y := Real.one_lt_rpow hx1 (by rw [hmR]; positivity)
  have hym : y ^ m = xP l := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), hmR, one_div, inv_mul_cancel₀ hmpos.ne',
      Real.rpow_one]
  have hx1m : xP l ^ (1 - 1 / mR l) = y ^ (m - 1) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), hmR]
    congr 1
    rw [Nat.cast_sub hm1, Nat.cast_one]
    field_simp
  have hgeom : (y ^ (m - 1) - 1) / (y - 1) = ∑ k ∈ Finset.range (m - 1), y ^ k :=
    (geom_sum_eq (ne_of_gt hy1) (m - 1)).symm
  rw [hx1m, mul_div_assoc, hgeom]
  have hα1 : alpha1 l = (2 * nOf l + 3 * l : ℝ) / (9 * (m : ℝ)) := by unfold alpha1; rw [hmR]
  have hα2 : alpha2 l = (6 * nOf l + l : ℝ) / (27 * (m : ℝ)) := by unfold alpha2; rw [hmR]
  rw [hα1, hα2]
  rcases Nat.lt_or_ge l 23 with hsmall | hbig
  · have hbase : (M l (nOf l) : ℝ) / 3 ^ nOf l ≤ (2 * nOf l + 3 * l : ℝ) / (9 * (m : ℝ)) * 1
        + (6 * nOf l + l : ℝ) / (27 * (m : ℝ)) * ((m - 1 : ℕ) : ℝ) := by
      simp only [hmdef]
      clear_value m y
      interval_cases l
      · exact small_case 7 4 101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 8 5 319 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 9 5 431 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 10 6 1357 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 11 6 1805 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 12 7 5095 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 13 8 14501 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 14 8 21109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 15 9 60191 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 16 10 159181 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 17 10 213341 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 18 11 579943 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 19 11 826391 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 20 12 2378821 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 21 13 5805215 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
      · exact small_case 22 13 8185039 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
    have hpowy : 1 ≤ y ^ (m - 1) := one_le_pow₀ hy1.le
    have hsumy : ((m - 1 : ℕ) : ℝ) ≤ ∑ k ∈ Finset.range (m - 1), y ^ k := by
      have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (m - 1)) => one_le_pow₀ (M₀ := ℝ) (n := k) hy1.le)
      simpa using this
    have ha1 : 0 ≤ (2 * nOf l + 3 * l : ℝ) / (9 * (m : ℝ)) := by positivity
    have ha2 : 0 ≤ (6 * nOf l + l : ℝ) / (27 * (m : ℝ)) := by positivity
    calc _ ≤ _ := hbase
      _ ≤ _ := by gcongr
  · obtain ⟨bs, hbs⟩ := blocks23_thm l hbig
    exact prop2_struct l (nOf l) hl0 hnl h2n h3 bs hbs y hy1.le hym

/-! ## Lemma 6 (without the concavity claim of the printed proof) -/

lemma geom_mul (y : ℝ) (k : ℕ) : y ^ k - 1 = (y - 1) * ∑ i ∈ Finset.range k, y ^ i := by
  rw [mul_comm, geom_sum_mul]

/-- The exact form of `f` with `y = x^{1/m}`, `T = Σ_{k<m} y^k`: `f(x) = 3 h (α₂ + (α₁ − α₂) y^{m−1}/T)`,
`h = (x^{1/n} − 1)/(y − 1)`. -/
lemma f6_eq (l : ℕ) (hl : 7 ≤ l) (x : ℝ) (hx1 : 1 < x) :
    f6 l x = 3 * ((x ^ (1 / (nOf l : ℝ)) - 1) / (x ^ (1 / mR l) - 1)) *
      (alpha2 l + (alpha1 l - alpha2 l) * ((x ^ (1 / mR l)) ^ (2 * nOf l - l - 1)
        / ∑ k ∈ Finset.range (2 * nOf l - l), (x ^ (1 / mR l)) ^ k)) := by
  have h2n : l < 2 * nOf l := l_lt_two_nOf l hl
  have hm1 : 1 ≤ 2 * nOf l - l := by omega
  have hmR : mR l = ((2 * nOf l - l : ℕ) : ℝ) := by unfold mR; push_cast [h2n.le]; ring
  have hmpos : (0 : ℝ) < ((2 * nOf l - l : ℕ) : ℝ) := by exact_mod_cast hm1
  unfold f6
  set m := 2 * nOf l - l with hmdef
  set y := x ^ (1 / mR l) with hy
  have hy1 : 1 < y := Real.one_lt_rpow hx1 (by rw [hmR]; positivity)
  have hym : y ^ m = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), hmR, one_div, inv_mul_cancel₀ hmpos.ne',
      Real.rpow_one]
  have hx1m : x ^ (1 - 1 / mR l) = y ^ (m - 1) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), hmR]
    congr 1
    rw [Nat.cast_sub hm1, Nat.cast_one]
    field_simp
  rw [hx1m]
  set T := ∑ k ∈ Finset.range m, y ^ k with hT
  set S := ∑ k ∈ Finset.range (m - 1), y ^ k with hS
  have hTS : T = S + y ^ (m - 1) := by
    rw [hT, hS]
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
  have hyS : y ^ (m - 1) - 1 = (y - 1) * S := geom_mul y (m - 1)
  have hxT : x - 1 = (y - 1) * T := by rw [← hym]; exact geom_mul y m
  have hy0 : y - 1 ≠ 0 := by linarith
  have hT0 : 0 < T := Finset.sum_pos (fun i _ => by positivity) (Finset.nonempty_range_iff.mpr (by omega))
  rw [hyS, hxT]
  have hT0' : S + y ^ (m - 1) ≠ 0 := by rw [← hTS]; exact hT0.ne'
  rw [hTS]
  field_simp
  ring

/-- `h ≤ m/n` (weighted AM–GM: `y^{m/n} ≤ (m/n) y + 1 − m/n`). -/
lemma h_le (l : ℕ) (hl : 7 ≤ l) (x : ℝ) (hx1 : 1 < x) :
    (x ^ (1 / (nOf l : ℝ)) - 1) / (x ^ (1 / mR l) - 1) ≤ ((2 * nOf l - l : ℕ) : ℝ) / nOf l := by
  have h2n : l < 2 * nOf l := l_lt_two_nOf l hl
  have hnl : nOf l ≤ l := nOf_le l
  have hm1 : 1 ≤ 2 * nOf l - l := by omega
  have hmR : mR l = ((2 * nOf l - l : ℕ) : ℝ) := by unfold mR; push_cast [h2n.le]; ring
  have hmpos : (0 : ℝ) < ((2 * nOf l - l : ℕ) : ℝ) := by exact_mod_cast hm1
  have hnpos : (0 : ℝ) < nOf l := by exact_mod_cast (show 0 < nOf l by omega)
  set m := 2 * nOf l - l with hmdef
  set y := x ^ (1 / mR l) with hy
  have hy1 : 1 < y := Real.one_lt_rpow hx1 (by rw [hmR]; positivity)
  have hym : y ^ m = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), hmR, one_div, inv_mul_cancel₀ hmpos.ne',
      Real.rpow_one]
  set c : ℝ := (m : ℝ) / nOf l with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hnpos]; exact_mod_cast (show m ≤ nOf l by omega)
  have hz : x ^ (1 / (nOf l : ℝ)) = y ^ c := by
    rw [← hym, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), hc]
    congr 1
    ring
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hc0 (by linarith : 0 ≤ 1 - c) (by linarith : (0 : ℝ) ≤ y)
    zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, mul_one] at hamgm
  rw [hz, div_le_iff₀ (by linarith)]
  linarith

/-- `y^{m−1}/Σ_{k<m} y^k ≤ 1/G` as soon as `G ≤ Σ_{i<m} (1/y)^i`. -/
lemma q_le (y : ℝ) (hy : 1 < y) (m : ℕ) (hm : 1 ≤ m) (G : ℝ) (hG0 : 0 < G)
    (hG : G ≤ ∑ i ∈ Finset.range m, (1 / y) ^ i) :
    y ^ (m - 1) / ∑ k ∈ Finset.range m, y ^ k ≤ 1 / G := by
  have hy0 : 0 < y := by linarith
  have hsum : ∑ k ∈ Finset.range m, y ^ k = y ^ (m - 1) * ∑ i ∈ Finset.range m, (1 / y) ^ i := by
    rw [← Finset.sum_range_reflect (fun i => (1 / y) ^ i) m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [div_pow, one_pow, show m - 1 - k = (m - 1 - k) from rfl]
    rw [mul_one_div, eq_div_iff (by positivity), ← pow_add]
    congr 1
    omega
  rw [hsum, div_mul_cancel_left₀ (by positivity), inv_eq_one_div]
  exact one_div_le_one_div_of_le hG0 hG

/-- The bound `f ≤ (6n+l)/(9n) + (8l/(9n))/G` for any `G` below `Σ_{i<m} (1/y)^i`. -/
lemma f6_le (l : ℕ) (hl : 7 ≤ l) (x : ℝ) (hx1 : 1 < x) (G : ℝ) (hG0 : 0 < G)
    (hG : ∀ y : ℝ, 1 < y → y ^ (2 * nOf l - l) = x → G ≤ ∑ i ∈ Finset.range (2 * nOf l - l), (1 / y) ^ i) :
    f6 l x ≤ (6 * nOf l + l : ℝ) / (9 * nOf l) + (8 * l / (9 * nOf l)) / G := by
  have h2n : l < 2 * nOf l := l_lt_two_nOf l hl
  have hnl : nOf l ≤ l := nOf_le l
  have hm1 : 1 ≤ 2 * nOf l - l := by omega
  have hmR : mR l = ((2 * nOf l - l : ℕ) : ℝ) := by unfold mR; push_cast [h2n.le]; ring
  have hmpos : (0 : ℝ) < ((2 * nOf l - l : ℕ) : ℝ) := by exact_mod_cast hm1
  have hnpos : (0 : ℝ) < nOf l := by exact_mod_cast (show 0 < nOf l by omega)
  rw [f6_eq l hl x hx1]
  set y := x ^ (1 / mR l) with hy
  have hy1 : 1 < y := Real.one_lt_rpow hx1 (by rw [hmR]; positivity)
  have hym : y ^ (2 * nOf l - l) = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), hmR, one_div, inv_mul_cancel₀ hmpos.ne',
      Real.rpow_one]
  have hq := q_le y hy1 _ hm1 G hG0 (hG y hy1 hym)
  have hh := h_le l hl x hx1
  rw [← hy] at hh
  have hq0 : 0 ≤ y ^ (2 * nOf l - l - 1) / ∑ k ∈ Finset.range (2 * nOf l - l), y ^ k := by positivity
  have hh0 : 0 ≤ (x ^ (1 / (nOf l : ℝ)) - 1) / (y - 1) := by
    apply div_nonneg _ (by linarith)
    have : 1 ≤ x ^ (1 / (nOf l : ℝ)) := Real.one_le_rpow hx1.le (by positivity)
    linarith
  have hα : alpha1 l - alpha2 l = 8 * l / (27 * ((2 * nOf l - l : ℕ) : ℝ)) := by
    unfold alpha1 alpha2; rw [hmR]; field_simp; ring
  have hα2 : alpha2 l = (6 * nOf l + l : ℝ) / (27 * ((2 * nOf l - l : ℕ) : ℝ)) := by unfold alpha2; rw [hmR]
  have hα0 : 0 ≤ alpha1 l - alpha2 l := by rw [hα]; positivity
  have hα20 : 0 ≤ alpha2 l := by rw [hα2]; positivity
  calc 3 * ((x ^ (1 / (nOf l : ℝ)) - 1) / (y - 1)) *
        (alpha2 l + (alpha1 l - alpha2 l) * (y ^ (2 * nOf l - l - 1) / ∑ k ∈ Finset.range (2 * nOf l - l), y ^ k))
      ≤ 3 * (((2 * nOf l - l : ℕ) : ℝ) / nOf l) * (alpha2 l + (alpha1 l - alpha2 l) * (1 / G)) := by
        gcongr
    _ = (6 * nOf l + l : ℝ) / (9 * nOf l) + (8 * l / (9 * nOf l)) / G := by
        rw [hα, hα2]
        field_simp
        ring

/-- `Σ_{i<m} (1/y)^i ≥ m/√3` when `y > 1`, `y^m < 3` (pair `i` with `m − 1 − i`). -/
lemma sum_inv_ge (y : ℝ) (hy : 1 < y) (m : ℕ) (hm3 : y ^ m < 3) :
    (m : ℝ) / Real.sqrt 3 ≤ ∑ i ∈ Finset.range m, (1 / y) ^ i := by
  set u := 1 / y with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one (by linarith)]; linarith
  have hum : 1 / 3 < u ^ m := by
    rw [hu, div_pow, one_pow, one_div_lt_one_div (by norm_num) (by positivity)]
    exact hm3
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hpair : ∀ i ∈ Finset.range m, 2 / Real.sqrt 3 ≤ u ^ i + u ^ (m - 1 - i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hprod : u ^ i * u ^ (m - 1 - i) = u ^ (m - 1) := by rw [← pow_add]; congr 1; omega
    have hge : 1 / 3 ≤ u ^ i * u ^ (m - 1 - i) := by
      rw [hprod]
      have : u ^ m ≤ u ^ (m - 1) := pow_le_pow_of_le_one hu0.le hu1 (Nat.sub_le m 1)
      linarith
    have hsq := two_mul_le_add_sq (Real.sqrt (u ^ i)) (Real.sqrt (u ^ (m - 1 - i)))
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), mul_assoc, ← Real.sqrt_mul (by positivity)] at hsq
    have h13 : Real.sqrt (1 / 3) ≤ Real.sqrt (u ^ i * u ^ (m - 1 - i)) := Real.sqrt_le_sqrt hge
    have he : 2 / Real.sqrt 3 = 2 * Real.sqrt (1 / 3) := by
      rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_one]; ring
    rw [he]
    linarith
  have h2 : 2 * ∑ i ∈ Finset.range m, u ^ i = ∑ i ∈ Finset.range m, (u ^ i + u ^ (m - 1 - i)) := by
    rw [Finset.sum_add_distrib, Finset.sum_range_reflect (fun i => u ^ i) m]
    ring
  have h3 : ∑ _i ∈ Finset.range m, 2 / Real.sqrt 3 ≤ ∑ i ∈ Finset.range m, (u ^ i + u ^ (m - 1 - i)) :=
    Finset.sum_le_sum hpair
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
  have : (m : ℝ) / Real.sqrt 3 = (m * (2 / Real.sqrt 3)) / 2 := by field_simp
  rw [this]
  linarith

lemma sqrt3_lt : Real.sqrt 3 < 17321 / 10000 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- Lemma 6 for `l ≥ 180`, uniformly. -/
lemma lemma6_large (l : ℕ) (hl : 180 ≤ l) (x : ℝ) (hx1 : 1 < x) (hx3 : x < 3) : f6 l x ≤ 9 / 10 := by
  have hl7 : 7 ≤ l := by omega
  have h2n : l < 2 * nOf l := l_lt_two_nOf l hl7
  have hnl : nOf l ≤ l := nOf_le l
  have hge := nOf_ge l (by omega)
  have hm1 : 1 ≤ 2 * nOf l - l := by omega
  have hmpos : (0 : ℝ) < ((2 * nOf l - l : ℕ) : ℝ) := by exact_mod_cast hm1
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hG0 : 0 < ((2 * nOf l - l : ℕ) : ℝ) / Real.sqrt 3 := by positivity
  refine le_trans (f6_le l hl7 x hx1 _ hG0 fun y hy hym => sum_inv_ge y hy _ (by rw [hym]; exact hx3)) ?_
  have hnpos : (0 : ℝ) < nOf l := by exact_mod_cast (show 0 < nOf l by omega)
  set N : ℝ := ((nOf l : ℕ) : ℝ) with hN
  set L : ℝ := ((l : ℕ) : ℝ) with hL
  set Mm : ℝ := ((2 * nOf l - l : ℕ) : ℝ) with hMm
  have hMmeq : Mm = 2 * N - L := by rw [hMm, hN, hL]; push_cast [h2n.le]; ring
  have hgeR : 6309 * L < 10000 * (N + 1) := by rw [hN, hL]; exact_mod_cast hge
  have hLge : 180 ≤ L := by rw [hL]; exact_mod_cast hl
  have hNint : 6309 * L - 9999 ≤ 10000 * N := by
    have : 6309 * l ≤ 10000 * nOf l + 9999 := by omega
    have h' : ((6309 * l : ℕ) : ℝ) ≤ ((10000 * nOf l + 9999 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    rw [hN, hL]
    linarith
  have hA : 2618 * L - 19998 ≤ 10000 * Mm := by rw [hMmeq]; linarith
  have hB : 32489 * L - 209979 ≤ 10000 * (21 * N - 10 * L) := by linarith
  have hA0 : 0 ≤ 2618 * L - 19998 := by linarith
  have hB0 : 0 ≤ 32489 * L - 209979 := by linarith
  have hprod : (2618 * L - 19998) * (32489 * L - 209979) ≤ (10000 * Mm) * (10000 * (21 * N - 10 * L)) :=
    mul_le_mul hA hB hB0 (by linarith)
  have hquad : 138568 * L * 100000 ≤ (2618 * L - 19998) * (32489 * L - 209979) := by
    nlinarith [sq_nonneg (L - 180)]
  have hkey : 138568 * L ≤ 1000 * Mm * (21 * N - 10 * L) := by nlinarith
  have hs3' := sqrt3_lt
  have hsqrt_bound : 8 * L * Real.sqrt 3 ≤ 8 * L * (17321 / 10000) := by
    apply mul_le_mul_of_nonneg_left hs3'.le (by positivity)
  have e : (6 * N + L) / (9 * N) + 8 * L / (9 * N) / (Mm / Real.sqrt 3)
      = (6 * (N * Mm) + L * Mm + 8 * L * Real.sqrt 3) / (9 * N * Mm) := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have hkey' : 138568 * L ≤ 21000 * (Mm * N) - 10000 * (Mm * L) := by nlinarith
  nlinarith

/-- Lemma 6 at one `l ∈ [161, 179]`, from a rational `r` with `3 r^m ≤ 1`. -/
lemma l6_case (l n0 : ℕ) (r : ℝ) (hl7 : 7 ≤ l) (h1 : 3 ^ n0 < 2 ^ l) (h2 : 2 ^ l < 3 ^ (n0 + 1))
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : 3 * r ^ (2 * n0 - l) ≤ 1)
    (hfin : (6 * n0 + l : ℝ) / (9 * n0) + (8 * l / (9 * n0)) / ((1 - r ^ (2 * n0 - l)) / (1 - r)) ≤ 9 / 10)
    (x : ℝ) (hx1 : 1 < x) (hx3 : x < 3) : f6 l x ≤ 9 / 10 := by
  have hn := nOf_eq (by omega) h1 h2
  have hG0 : 0 < (1 - r ^ (2 * n0 - l)) / (1 - r) := by
    apply div_pos _ (by linarith)
    have : r ^ (2 * n0 - l) ≤ 1 / 3 := by linarith
    linarith
  have hb := f6_le l hl7 x hx1 ((1 - r ^ (2 * n0 - l)) / (1 - r)) hG0 (by
    intro y hy hym
    rw [hn] at hym ⊢
    have hry : r ≤ 1 / y := by
      by_contra hc
      push Not at hc
      have h' : (1 / y) ^ (2 * n0 - l) ≤ r ^ (2 * n0 - l) := pow_le_pow_left₀ (by positivity) hc.le _
      rw [div_pow, one_pow, hym] at h'
      have : 1 / 3 < 1 / x := one_div_lt_one_div_of_lt (by linarith) hx3
      linarith
    have hgeo : (1 - r ^ (2 * n0 - l)) / (1 - r) = ∑ i ∈ Finset.range (2 * n0 - l), r ^ i := by
      rw [geom_sum_eq (by linarith), show (1 : ℝ) - r ^ (2 * n0 - l) = -(r ^ (2 * n0 - l) - 1) by ring,
        show (1 : ℝ) - r = -(r - 1) by ring, neg_div_neg_eq]
    rw [hgeo]
    exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hr0 hry i)
  rw [hn] at hb
  exact hb.trans hfin

/-- `h` is non-increasing: for `1 < y₁ ≤ y`, `(y^c − 1)/(y − 1) ≤ (y₁^c − 1)/(y₁ − 1)`, `0 ≤ c ≤ 1`. -/
lemma h_mono (c y1 y : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hy1 : 1 < y1) (hy : y1 ≤ y) :
    (y ^ c - 1) / (y - 1) ≤ (y1 ^ c - 1) / (y1 - 1) := by
  have hy10 : 0 < y1 := by linarith
  have hy0 : 0 < y := by linarith
  set A := y1 ^ c with hA
  have hA0 : 0 < A := by positivity
  have t1 : y ^ c ≤ A * (c * (y / y1) + (1 - c)) := by
    have h := Real.geom_mean_le_arith_mean2_weighted hc0 (by linarith : 0 ≤ 1 - c) (by positivity : 0 ≤ y / y1)
      zero_le_one (by ring)
    rw [Real.one_rpow, mul_one, mul_one, Real.div_rpow hy0.le hy10.le] at h
    rw [← hA] at h
    have : y ^ c = A * (y ^ c / A) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h hA0.le
  have t2 : 1 ≤ (1 - c) * A + c * (A / y1) := by
    have h := Real.geom_mean_le_arith_mean2_weighted (by linarith : 0 ≤ 1 - c) hc0 hA0.le
      (by positivity : 0 ≤ A / y1) (by ring)
    have e : A ^ (1 - c) * (A / y1) ^ c = 1 := by
      rw [Real.div_rpow hA0.le hy10.le, hA, ← Real.rpow_mul hy10.le, ← Real.rpow_mul hy10.le, mul_div_assoc',
        ← Real.rpow_add hy10, show c * (1 - c) + c * c = c by ring, div_self (by positivity)]
    linarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have key : (A - 1) * (y - 1) - (A * (c * (y / y1) + (1 - c)) - 1) * (y1 - 1)
      = ((1 - c) * A + c * (A / y1) - 1) * (y - y1) := by
    field_simp
    ring
  have hk : 0 ≤ ((1 - c) * A + c * (A / y1) - 1) * (y - y1) := mul_nonneg (by linarith) (by linarith)
  have hmul : (y ^ c - 1) * (y1 - 1) ≤ (A * (c * (y / y1) + (1 - c)) - 1) * (y1 - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- Lemma 6 at `l = 163` (two pieces). -/
lemma lemma6_163 (x : ℝ) (hx1 : 1 < x) (hx3 : x < 3) : f6 163 x ≤ 9 / 10 := by
  have hn : nOf 163 = 102 := nOf_eq (by norm_num) (by norm_num) (by norm_num)
  have hmR : mR 163 = 41 := by unfold mR; rw [hn]; norm_num
  have ha1 : alpha1 163 = 693 / 369 := by unfold alpha1; rw [hn, hmR]; norm_num
  have ha2 : alpha2 163 = 775 / 1107 := by unfold alpha2; rw [hn, hmR]; norm_num
  rw [f6_eq 163 (by norm_num) x hx1, hn, ha1, ha2, hmR, show 2 * 102 - 163 - 1 = 40 by norm_num,
    show 2 * 102 - 163 = 41 by norm_num, Nat.cast_ofNat]
  set y := x ^ ((1 : ℝ) / 41) with hy
  have hy1 : 1 < y := Real.one_lt_rpow hx1 (by norm_num)
  have hym : y ^ 41 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hz : x ^ ((1 : ℝ) / 102) = y ^ ((41 : ℝ) / 102) := by
    rw [← hym, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  rw [hz]
  have hy2 : y ≤ 64197353 / 62500000 := by
    by_contra hc
    push Not at hc
    have h1 : (64197353 / 62500000 : ℝ) ^ 41 ≤ y ^ 41 := pow_le_pow_left₀ (by norm_num) hc.le _
    rw [hym] at h1
    have hq : (3 : ℚ) ≤ (64197353 / 62500000 : ℚ) ^ 41 := by decide +kernel
    have h3 := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at h3
    linarith
  have hQ : ∀ yb : ℝ, 1 < yb → y ≤ yb →
      y ^ 40 / ∑ k ∈ Finset.range 41, y ^ k ≤ 1 / ((1 - (1 / yb) ^ 41) / (1 - 1 / yb)) := by
    intro yb hyb hle
    have hgeo : ∑ i ∈ Finset.range 41, (1 / yb) ^ i = (1 - (1 / yb) ^ 41) / (1 - 1 / yb) := by
      have h1 : 1 / yb ≠ 1 := by intro h; rw [div_eq_one_iff_eq (by linarith)] at h; linarith
      rw [geom_sum_eq h1, show (1 : ℝ) - (1 / yb) ^ 41 = -((1 / yb) ^ 41 - 1) by ring,
        show (1 : ℝ) - 1 / yb = -(1 / yb - 1) by ring, neg_div_neg_eq]
    rw [← hgeo]
    apply q_le y hy1 41 (by norm_num) _ (by positivity)
    exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (by positivity)
      (one_div_le_one_div_of_le (by linarith) hle) i
  have hh0 : 0 ≤ (y ^ ((41 : ℝ) / 102) - 1) / (y - 1) := by
    apply div_nonneg _ (by linarith)
    have : 1 ≤ y ^ ((41 : ℝ) / 102) := Real.one_le_rpow hy1.le (by norm_num)
    linarith
  have hQ0 : 0 ≤ y ^ 40 / ∑ k ∈ Finset.range 41, y ^ k := by positivity
  rcases le_total y (126697353 / 125000000) with hle | hge
  · -- first piece: h ≤ 41/102, q ≤ q(y₁)
    have hh : (y ^ ((41 : ℝ) / 102) - 1) / (y - 1) ≤ 41 / 102 := by
      have hamgm := Real.geom_mean_le_arith_mean2_weighted (by norm_num : (0 : ℝ) ≤ 41 / 102)
        (by norm_num : (0 : ℝ) ≤ 1 - 41 / 102) (by linarith : (0 : ℝ) ≤ y) zero_le_one (by ring)
      rw [Real.one_rpow, mul_one, mul_one] at hamgm
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hq := hQ (126697353 / 125000000) (by norm_num) hle
    have hnumQ : (3 * (41 / 102) * (775 / 1107 + (693 / 369 - 775 / 1107) *
        (1 / ((1 - (1 / (126697353 / 125000000 : ℚ)) ^ 41) / (1 - 1 / (126697353 / 125000000 : ℚ))))) : ℚ)
        ≤ 9 / 10 := by decide +kernel
    have hnum := (Rat.cast_le (K := ℝ)).mpr hnumQ
    push_cast at hnum
    calc _ ≤ 3 * (41 / 102) * (775 / 1107 + (693 / 369 - 775 / 1107) *
            (1 / ((1 - (1 / (126697353 / 125000000 : ℝ)) ^ 41) / (1 - 1 / (126697353 / 125000000 : ℝ))))) := by
          gcongr
      _ ≤ 9 / 10 := hnum
  · -- second piece: h ≤ h(y₁) ≤ (s₁ − 1)/(y₁ − 1), q ≤ q(y₂)
    have hs1 : (126697353 / 125000000 : ℝ) ^ ((41 : ℝ) / 102) ≤ 125679519 / 125000000 := by
      have h41 : ((126697353 / 125000000 : ℝ) ^ ((41 : ℝ) / 102)) ^ (102 : ℕ)
          = (126697353 / 125000000 : ℝ) ^ (41 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]; norm_num
      have hcmpQ : (126697353 / 125000000 : ℚ) ^ (41 : ℕ) ≤ (125679519 / 125000000 : ℚ) ^ (102 : ℕ) := by
        decide +kernel
      have hcmp := (Rat.cast_le (K := ℝ)).mpr hcmpQ
      push_cast at hcmp
      rw [← h41] at hcmp
      exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).mp hcmp
    have hh : (y ^ ((41 : ℝ) / 102) - 1) / (y - 1) ≤ (125679519 / 125000000 - 1) / (126697353 / 125000000 - 1) := by
      calc (y ^ ((41 : ℝ) / 102) - 1) / (y - 1)
          ≤ ((126697353 / 125000000 : ℝ) ^ ((41 : ℝ) / 102) - 1) / (126697353 / 125000000 - 1) :=
            h_mono _ _ y (by norm_num) (by norm_num) (by norm_num) hge
        _ ≤ (125679519 / 125000000 - 1) / (126697353 / 125000000 - 1) := by gcongr
    have hq := hQ (64197353 / 62500000) (by norm_num) hy2
    have hnumQ : (3 * ((125679519 / 125000000 - 1) / (126697353 / 125000000 - 1)) * (775 / 1107 + (693 / 369 - 775 / 1107) *
        (1 / ((1 - (1 / (64197353 / 62500000 : ℚ)) ^ 41) / (1 - 1 / (64197353 / 62500000 : ℚ))))) : ℚ)
        ≤ 9 / 10 := by decide +kernel
    have hnum := (Rat.cast_le (K := ℝ)).mpr hnumQ
    push_cast at hnum
    calc _ ≤ 3 * ((125679519 / 125000000 - 1) / (126697353 / 125000000 - 1)) * (775 / 1107 + (693 / 369 - 775 / 1107) *
            (1 / ((1 - (1 / (64197353 / 62500000 : ℝ)) ^ 41) / (1 - 1 / (64197353 / 62500000 : ℝ))))) := by
          gcongr
      _ ≤ 9 / 10 := hnum

theorem lemma6_thm : lemma6 := by
  intro x hx1 hx3 l hl
  rcases Nat.lt_or_ge l 180 with hsmall | hbig
  · interval_cases l
    · exact l6_case 161 101 (24339/25000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 162 102 (974181/1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact lemma6_163 x hx1 hx3
    · exact l6_case 164 103 (974181/1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 165 104 (487387/500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 166 104 (974181/1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 167 105 (487387/500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 168 105 (974181/1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 169 106 (487387/500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 170 107 (48767/50000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 171 107 (487387/500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 172 108 (48767/50000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 173 109 (975881/1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 174 109 (48767/50000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 175 110 (975881/1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 176 111 (2441/2500) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 177 111 (975881/1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 178 112 (2441/2500) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
    · exact l6_case 179 112 (975881/1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx1 hx3
  · exact lemma6_large l hbig x hx1 hx3

end LaboHH
