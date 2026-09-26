import Mathlib
import Labo.Blueprint

/-!
# LABO-COLLATZ · S2 · A4 Formaliste — the bridge B1, B2, B3 (+ barrier witnesses)

No `sorry`, no `native_decide`.  `decide` is used ONLY on the finite, explicitly named
`*_witness` statements (cousin bench, PROTOCOLE_v2 §3).
-/

namespace LaboBP

/-- One step of `T`, doubled. -/
theorem two_mul_T_even (x : ℤ) (h : x % 2 = 0) : 2 * T x = x := by
  unfold T; split_ifs <;> omega

theorem two_mul_T_odd (x : ℤ) (h : x % 2 = 1) : 2 * T x = 3 * x + 1 := by
  unfold T; split_ifs <;> omega

theorem follows_nil (x : ℤ) : Follows x [] := by simp [Follows, pw]

theorem follows_cons (x : ℤ) (b : Bool) (w : List Bool) :
    Follows x (b :: w) ↔ (x % 2 == 1) = b ∧ Follows (T x) w := by
  simp [Follows, pw]

theorem C_cons_true (w : List Bool) : (C (true :: w) : ℤ) = 3 ^ (w.count true) + 2 * C w := by
  simp [C]

theorem C_cons_false (w : List Bool) : (C (false :: w) : ℤ) = 2 * C w := by
  simp [C]

/-- **B1 (bridge), proved.** -/
theorem B1 : B1_statement := by
  intro x w
  induction w generalizing x with
  | nil => intro _; simp [C]
  | cons b w ih =>
    intro h
    rw [follows_cons] at h
    obtain ⟨hb, hw⟩ := h
    have e := ih (T x) hw
    rw [List.length_cons, Function.iterate_succ_apply]
    cases b with
    | false =>
      have hx : x % 2 = 0 := by
        have : ¬ x % 2 = 1 := by simpa using hb
        omega
      have h2 := two_mul_T_even x hx
      have hr : (false :: w).count true = w.count true := by simp
      rw [C_cons_false, hr]
      linear_combination 2 * e + 3 ^ (w.count true) * h2
    | true =>
      have hx : x % 2 = 1 := by simpa using hb
      have h2 := two_mul_T_odd x hx
      have hr : (true :: w).count true = w.count true + 1 := by simp
      rw [C_cons_true, hr]
      linear_combination 2 * e + 3 ^ (w.count true) * h2

/-- **B2 (cycle equation), proved.** -/
theorem B2 : B2_statement := by
  intro x w h
  have h1 := B1 x w h
  unfold d
  constructor
  · intro hc
    rw [hc] at h1
    linear_combination h1
  · intro hc
    have h3 : (2 : ℤ) ^ w.length * T^[w.length] x = 2 ^ w.length * x := by
      linear_combination h1 - hc
    exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) h3

/-- `d(w) ≠ 0` for a nonempty word (`2^N` even, `3^r` odd). -/
theorem d_ne_zero (w : List Bool) (hne : w ≠ []) : d w ≠ 0 := by
  obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold d
  rw [List.length_cons, pow_succ]
  obtain ⟨k, hk⟩ := (Odd.pow (⟨1, by norm_num⟩ : Odd (3 : ℤ)) : Odd ((3 : ℤ) ^ (b :: v).count true))
  rw [hk]
  generalize (2 : ℤ) ^ v.length = a
  omega

/-- **B3, proved.** A positive cycle has `d(w) > 0`. -/
theorem B3 : B3_statement := by
  intro x w hx h hne hc
  have e := (B2 x w h).mp hc
  have hC : (0 : ℤ) ≤ (C w : ℤ) := Int.natCast_nonneg _
  rcases lt_or_gt_of_ne (d_ne_zero w hne) with hneg | hpos
  · have := mul_neg_of_pos_of_neg hx hneg
    linarith
  · exact hpos

/-- `C` equals the closed formula `Σ_j 2^{p_j} 3^{r-1-j}`. -/
theorem C_eq_Csum : C_eq_Csum_statement := by
  intro w
  induction w with
  | nil => simp [C, Csum]
  | cons b w ih =>
    unfold Csum
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.drop_succ_cons, List.getD_cons_zero, pow_zero, one_mul,
      zero_add]
    have : (∑ i ∈ Finset.range w.length,
        if w.getD i false then 2 ^ (i + 1) * 3 ^ ((w.drop (i + 1)).count true) else 0)
        = 2 * Csum w := by
      unfold Csum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs <;> ring
    rw [this, ← ih]
    cases b <;> (simp [C]; try ring)

/-! ## Necessity of the hypotheses (negative controls) -/

/-- T★ needs `true ∈ w`: `[false]` has `d = 1 > 0`, `d ∣ C = 0`, is not trivial, and is the cycle of 0. -/
theorem Tstar_needs_one_witness :
    0 < d [false] ∧ d [false] ∣ (C [false] : ℤ) ∧ Follows 0 [false] ∧ T^[1] 0 = 0 ∧
      ¬ TrivialWord [false] := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨k, n, h⟩
  have hl := congrArg List.length h
  simp at hl
  omega

/-! ## Barrier witnesses (finite, named; `decide` allowed here only) -/

/-- The trivial cycle: `w = 10`, `d = 1`, `C = 1`, `x = C/d = 1`. -/
theorem trivial_cycle_witness :
    Follows 1 [true, false] ∧ T^[2] 1 = 1 ∧ d [true, false] = 1 ∧ C [true, false] = 1 := by decide

/-- C1: `T(−1) = −1`, word `1`, `d = −1`. -/
theorem C1_minus1_witness :
    T (-1) = -1 ∧ Follows (-1) [true] ∧ d [true] = -1 ∧ C [true] = 1 := by decide

/-- C1: `−5 → −7 → −10 → −5`, word `110`, `d = −1`, `C = 5`. -/
theorem C1_minus5_witness :
    T^[3] (-5) = -5 ∧ Follows (-5) [true, true, false] ∧ d [true, true, false] = -1 ∧
      C [true, true, false] = 5 := by decide

/-- The word of the cycle of `−17`. -/
def w17 : List Bool := [true, true, true, true, false, true, true, true, false, false, false]

/-- C1: `T^11(−17) = −17`, word `11110111000`, `d = 2^11 − 3^7 = −139`, `C = 2363 = 17·139`. -/
theorem C1_minus17_witness :
    T^[11] (-17) = -17 ∧ Follows (-17) w17 ∧ w17.length = 11 ∧ w17.count true = 7 ∧
      d w17 = -139 ∧ C w17 = 2363 ∧ (139 ∣ C w17) := by decide

/-- C1 barrier for B3: the hypothesis `0 < x` cannot be dropped (cycle of `−17`, `d < 0`). -/
theorem C1_B3_barrier_witness :
    ∃ (x : ℤ) (w : List Bool), Follows x w ∧ w ≠ [] ∧ T^[w.length] x = x ∧ d w < 0 ∧
      d w ∣ (C w : ℤ) :=
  ⟨-17, w17, by decide, by decide, by decide, by decide, ⟨-17, by decide⟩⟩

/-- C3 (5x+1): `1 → 3 → 8 → 4 → 2 → 1`, word `11000`, `d = 2^5 − 5^2 = 7`. -/
theorem C3_one_witness : T5^[5] 1 = 1 ∧ (2 : ℤ) ^ 5 - 5 ^ 2 = 7 := by decide

/-- C3: cycle of 13, word `1110000`, `d = 2^7 − 5^3 = 3`. -/
theorem C3_13_witness : T5^[7] 13 = 13 ∧ (2 : ℤ) ^ 7 - 5 ^ 3 = 3 := by decide

/-- C3: cycle of 17, word `1100100`, `d = 2^7 − 5^3 = 3`. -/
theorem C3_17_witness : T5^[7] 17 = 17 ∧ (2 : ℤ) ^ 7 - 5 ^ 3 = 3 := by decide

/-- C4 (3x+5): `1 → 4 → 2 → 1`, word `100`, `d = 5 = k`, `x · d = k · C(w)`. -/
def T35 (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (3 * x + 5) / 2

theorem C4_3x5_witness :
    T35^[3] 1 = 1 ∧ d [true, false, false] = 5 ∧ C [true, false, false] = 1 ∧
      (1 : ℤ) * d [true, false, false] = 5 * C [true, false, false] := by decide

end LaboBP
