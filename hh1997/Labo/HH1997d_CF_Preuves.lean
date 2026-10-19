import Mathlib
import Labo.HH1997d_Pont_Preuves

/-!
# LABO-COLLATZ · HH1997d · formaliste (2026-10-19) — the continued-fraction gap of `log₂ 3`, and Theorem 1

Proves `cf_gap_all` (frozen in `Labo/HH1997d_Pont_Enonces.lean`) from Mathlib's continued-fraction API, hence
Theorem 1 (`thm1`, frozen in `Labo/HH1997d_Enonces.lean`) without hypothesis.  Not in Mathlib v4.34; done here:
1. the numerators and denominators of `GenContFract.of θ` are integers (induction on `contsAux_recurrence`, partial
   numerators `1`, integer partial denominators);
2. the exact error `q_kθ − p_k = (−1)^k / E_k` with `0 < E_k < q_k + q_{k+1}` (from Mathlib's `sub_convs_eq`, plus
   `fr⁻¹ < ⌊fr⁻¹⌋ + 1`), and `q_k < q_{k+1}` for `k ≥ 1`;
3. best approximation: for `1 ≤ q < q_{k+1}`, write `(p, q) = u(p_k, q_k) + w(p_{k+1}, q_{k+1})` with integers `u, w`
   (determinant `±1`, `SimpContFract.determinant`); `u` and `w` have opposite signs (or `w = 0`), so
   `|qθ − p| = |u/E_k − w/E_{k+1}| ≥ 1/E_k > 1/(q_k + q_{k+1})`.
`θ = log₂ 3` is irrational (`theta_irrational`), so the expansion never terminates.
-/

namespace LaboHH

open GenContFract

lemma s_some (n : ℕ) : ∃ gp, (GenContFract.of theta).s.get? n = some gp :=
  Option.ne_none_iff_exists'.mp (theta_not_terminated n)

/-- The continuants of `GenContFract.of θ` are integers. -/
lemma contsAux_int (n : ℕ) :
    ((∃ z : ℤ, ((GenContFract.of theta).contsAux n).a = z) ∧
      (∃ z : ℤ, ((GenContFract.of theta).contsAux n).b = z)) ∧
    ((∃ z : ℤ, ((GenContFract.of theta).contsAux (n + 1)).a = z) ∧
      (∃ z : ℤ, ((GenContFract.of theta).contsAux (n + 1)).b = z)) := by
  induction n with
  | zero =>
    rw [zeroth_contAux_eq_one_zero, first_contAux_eq_h_one, of_h_eq_floor]
    exact ⟨⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩, ⟨⟨⌊theta⌋, rfl⟩, ⟨1, by simp⟩⟩⟩
  | succ n ih =>
    obtain ⟨⟨⟨a0, ha0⟩, ⟨b0, hb0⟩⟩, ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩⟩ := ih
    refine ⟨⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩, ?_⟩
    obtain ⟨gp, hgp⟩ := s_some n
    obtain ⟨hga, z, hgb⟩ := of_partNum_eq_one_and_exists_int_partDen_eq hgp
    rw [contsAux_recurrence hgp rfl rfl]
    refine ⟨⟨z * a1 + a0, ?_⟩, ⟨z * b1 + b0, ?_⟩⟩
    · simp only [hga, hgb, ha0, ha1]; push_cast; ring
    · simp only [hga, hgb, hb0, hb1]; push_cast; ring

lemma nums_int (n : ℕ) : ∃ z : ℤ, (GenContFract.of theta).nums n = z := by
  rw [num_eq_conts_a, nth_cont_eq_succ_nth_contAux]
  exact (contsAux_int n).2.1

lemma dens_int (n : ℕ) : ∃ z : ℤ, (GenContFract.of theta).dens n = z := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  exact (contsAux_int n).2.2

/-- The exact error of the convergents of `θ`. -/
lemma cf_err (n : ℕ) : ∃ E : ℝ, 0 < E ∧ E < qCF n + qCF (n + 1) ∧
    qCF n * theta - (GenContFract.of theta).nums n = (-1) ^ n / E ∧ (1 ≤ n → qCF n < qCF (n + 1)) := by
  obtain ⟨gp, s_nth_eq⟩ := s_some n
  have gp_a : gp.a = 1 := (of_partNum_eq_one_and_exists_int_partDen_eq s_nth_eq).1
  have hrec := contsAux_recurrence s_nth_eq rfl rfl
  have hB : qCF n = ((GenContFract.of theta).contsAux (n + 1)).b := by
    unfold qCF
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have hnB : qCF (n + 1)
      = ((GenContFract.of theta).contsAux n).b + gp.b * ((GenContFract.of theta).contsAux (n + 1)).b := by
    unfold qCF
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, hrec, gp_a]
    simp only
    ring
  obtain ⟨ifp_succ_n, succ_nth_stream_eq, hb_eq⟩ :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some s_nth_eq
  obtain ⟨ifp_n, stream_nth_eq, fr_ne, of_eq⟩ := IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  have hsub := sub_convs_eq stream_nth_eq
  simp only [fr_ne, ↓reduceIte] at hsub
  have hfr : 0 < ifp_n.fr := lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg stream_nth_eq) (Ne.symm fr_ne)
  have hBpos : 0 < qCF n := qCF_pos n
  have hpB : 0 ≤ ((GenContFract.of theta).contsAux n).b := zero_le_of_contsAux_b
  have hfloor : (ifp_succ_n.b : ℝ) = ((⌊ifp_n.fr⁻¹⌋ : ℤ) : ℝ) := by rw [← of_eq]; rfl
  have hlt : ifp_n.fr⁻¹ < gp.b + 1 := by rw [← hb_eq, hfloor]; exact Int.lt_floor_add_one _
  have hge : (1 : ℝ) ≤ gp.b := by
    rw [← hb_eq]
    exact_mod_cast IntFractPair.one_le_succ_nth_stream_b succ_nth_stream_eq
  rw [← hB] at hsub
  refine ⟨ifp_n.fr⁻¹ * qCF n + ((GenContFract.of theta).contsAux n).b, by positivity, ?_, ?_, ?_⟩
  · rw [hnB, ← hB]
    nlinarith [mul_lt_mul_of_pos_right hlt hBpos]
  · have hconv : (GenContFract.of theta).convs n = (GenContFract.of theta).nums n / qCF n := rfl
    rw [hconv] at hsub
    have hE : 0 < ifp_n.fr⁻¹ * qCF n + ((GenContFract.of theta).contsAux n).b := by positivity
    have := congrArg (fun t => qCF n * t) hsub
    beta_reduce at this
    rw [mul_sub, mul_div_cancel₀ _ hBpos.ne'] at this
    rw [this]
    field_simp
  · intro hn
    have hfib : (Nat.fib n : ℝ) ≤ ((GenContFract.of theta).contsAux n).b :=
      fib_le_of_contsAux_b (Or.inr (theta_not_terminated (n - 2)))
    have h1 : (1 : ℝ) ≤ Nat.fib n := by exact_mod_cast Nat.fib_pos.mpr hn
    rw [hnB, ← hB]
    nlinarith [mul_le_mul_of_nonneg_right hge hBpos.le]

lemma cf_det (n : ℕ) :
    (GenContFract.of theta).nums n * qCF (n + 1) - qCF n * (GenContFract.of theta).nums (n + 1)
      = (-1) ^ (n + 1) :=
  SimpContFract.determinant (s := SimpContFract.of theta) (theta_not_terminated n)

theorem cf_gap_all_thm : cf_gap_all := by
  intro k hk p q hq hqk
  obtain ⟨E0, hE0, hE0lt, hδ0, hmono⟩ := cf_err k
  obtain ⟨E1, hE1, -, hδ1, -⟩ := cf_err (k + 1)
  have hlt := hmono hk
  have hdet := cf_det k
  have hQ0pos := qCF_pos k
  have hQ1pos := qCF_pos (k + 1)
  obtain ⟨P0, hP0⟩ := nums_int k
  obtain ⟨Q0, hQ0⟩ := dens_int k
  obtain ⟨P1, hP1⟩ := nums_int (k + 1)
  obtain ⟨Q1, hQ1⟩ := dens_int (k + 1)
  simp only [qCF, hP0, hQ0, hP1, hQ1] at hδ0 hδ1 hE0lt hqk hlt hdet hQ0pos hQ1pos ⊢
  have hdetZ : P0 * Q1 - Q0 * P1 = (-1) ^ (k + 1) := by exact_mod_cast hdet
  have hQ0Z : 1 ≤ Q0 := by
    have : (0 : ℤ) < Q0 := by exact_mod_cast hQ0pos
    omega
  have hQ1Z : 1 ≤ Q1 := by
    have : (0 : ℤ) < Q1 := by exact_mod_cast hQ1pos
    omega
  have hqQ1 : q < Q1 := by
    have : (q : ℝ) < Q1 := lt_of_le_of_lt hqk hlt
    exact_mod_cast this
  set D : ℤ := (-1) ^ (k + 1) with hDdef
  have hD2 : D * D = 1 := by
    rw [hDdef, ← pow_add, ← two_mul, pow_mul]
    norm_num
  set u : ℤ := D * (p * Q1 - q * P1) with hu
  set w : ℤ := D * (q * P0 - p * Q0) with hw
  have hq_eq : u * Q0 + w * Q1 = q := by
    rw [hu, hw]
    linear_combination (D * q) * hdetZ + q * hD2
  have hp_eq : u * P0 + w * P1 = p := by
    rw [hu, hw]
    linear_combination (D * p) * hdetZ + p * hD2
  have hq_eqR : (u : ℝ) * Q0 + w * Q1 = q := by exact_mod_cast hq_eq
  have hp_eqR : (u : ℝ) * P0 + w * P1 = p := by exact_mod_cast hp_eq
  -- `qθ − p = (−1)^k (u/E₀ − w/E₁)`
  have hX : (q : ℝ) * theta - p = (-1) ^ k * ((u : ℝ) / E0 - w / E1) := by
    rw [← hq_eqR, ← hp_eqR]
    have h0 : (u : ℝ) * ((Q0 : ℝ) * theta - P0) = u * ((-1) ^ k / E0) := by rw [hδ0]
    have h1 : (w : ℝ) * ((Q1 : ℝ) * theta - P1) = w * ((-1) ^ (k + 1) / E1) := by rw [hδ1]
    rw [pow_succ] at h1
    linear_combination h0 + h1
  have habs : |(q : ℝ) * theta - p| = |(u : ℝ) / E0 - w / E1| := by
    rw [hX, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs]
  have hkey : 1 / E0 ≤ |(u : ℝ) / E0 - w / E1| := by
    rcases le_or_gt w 0 with hw0 | hw0
    · have hu1 : 1 ≤ u := by
        by_contra hcon
        have hu0 : u ≤ 0 := by omega
        nlinarith
      have hu1R : (1 : ℝ) ≤ u := by exact_mod_cast hu1
      have hw0R : (w : ℝ) ≤ 0 := by exact_mod_cast hw0
      have a1 : 1 / E0 ≤ (u : ℝ) / E0 := div_le_div_of_nonneg_right hu1R hE0.le
      have a2 : (w : ℝ) / E1 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hw0R hE1.le
      exact le_trans (by linarith) (le_abs_self _)
    · have hu1 : u ≤ -1 := by
        by_contra hcon
        have hu0 : 0 ≤ u := by omega
        nlinarith
      have hu1R : (u : ℝ) ≤ -1 := by exact_mod_cast hu1
      have hw0R : (0 : ℝ) ≤ w := by exact_mod_cast hw0.le
      have a1 : (u : ℝ) / E0 ≤ -1 / E0 := div_le_div_of_nonneg_right hu1R hE0.le
      have a2 : 0 ≤ (w : ℝ) / E1 := div_nonneg hw0R hE1.le
      have a3 : -1 / E0 = -(1 / E0) := by ring
      exact le_trans (by linarith) (neg_le_abs _)
  exact lt_of_lt_of_le (one_div_lt_one_div_of_lt hE0 hE0lt) hkey

/-- Theorem 1 (Crandall), unconditional. -/
theorem thm1_thm : thm1 := thm1_from_gap_all_thm cf_gap_all_thm

end LaboHH
