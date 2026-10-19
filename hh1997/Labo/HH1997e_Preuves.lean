import Mathlib
import Labo.HH1997e_Enonces
import Labo.HH1997c_Preuves

/-!
# LABO-COLLATZ · HH1997e · formaliste (2026-10-19) — PROOF of (A′) ⇔ ¬(A) (`Labo/HH1997e_Enonces.lean`)

Reused: Lemma 9 (15) (`lemma9_15_gen_thm`), Lemma 2 (`lemma2_cycle_thm`, `orbit_formula`, `num_parity`,
`phi_rot_parity`) of the first batch; Lemma 1 (`lemma1_core`, `cycle_point_aux`, `cycle_ncard`) of the second;
`phi_pos_iff` of the third.  Axiom log: `Labo/HH1997e_Axiomes.lean`.
-/

namespace LaboHH

open LaboBP

lemma collatzQ_one : collatzQ 1 = 2 := by unfold collatzQ; norm_num
lemma collatzQ_two : collatzQ 2 = 1 := by unfold collatzQ; norm_num

lemma iter_one (i : ℕ) : collatzQ^[2 * i] (1 : ℚ) = 1 ∧ collatzQ^[2 * i + 1] (1 : ℚ) = 2 := by
  induction i with
  | zero => exact ⟨rfl, collatzQ_one⟩
  | succ i ih =>
    have h1 : collatzQ^[2 * (i + 1)] (1 : ℚ) = 1 := by
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, Function.iterate_succ_apply', ih.2, collatzQ_two]
    exact ⟨h1, by rw [Function.iterate_succ_apply', h1, collatzQ_one]⟩

lemma cycle_one : cycle (1 : ℚ) = {1, 2} := by
  ext y
  simp only [cycle, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · exact Or.inl (iter_one k).1
    · exact Or.inr (iter_one k).2
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, collatzQ_one⟩

lemma cycle_two : cycle (2 : ℚ) = {1, 2} := by
  ext y
  simp only [cycle, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hshift : ∀ i, collatzQ^[i] (2 : ℚ) = collatzQ^[i + 1] (1 : ℚ) := fun i => by
    rw [Function.iterate_succ_apply, collatzQ_one]
  constructor
  · rintro ⟨i, rfl⟩
    rw [hshift]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · exact Or.inr (iter_one k).2
    · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]; exact Or.inl (iter_one (k + 1)).1
  · rintro (rfl | rfl)
    · exact ⟨1, collatzQ_two⟩
    · exact ⟨0, rfl⟩

theorem Aprime_equiv_thm : Aprime_equiv := by
  constructor
  · rintro ⟨x₀, hx0, hper, hne⟩
    obtain ⟨hp, horb, hx⟩ := lemma1_core (x₀ : ℚ) hper
    set p := Function.minimalPeriod collatzQ (x₀ : ℚ) with hpdef
    set w := parityWord (x₀ : ℚ) p with hwdef
    have hwl : w.length = p := by simp [w]
    have hw : w ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [hwl] at this
      simp at this
      omega
    have horb' : ∀ i, i ≤ w.length → collatzQ^[i] (x₀ : ℚ) = phiMap (w.take i) (x₀ : ℚ) := fun i hi =>
      horb i (by rw [hwl] at hi; exact hi)
    have hpt : ∀ i, i ≤ w.length → collatzQ^[i] (x₀ : ℚ) = (phi (w.rotate i) : ℚ) / (d w : ℚ) :=
      fun i hi => cycle_point_aux _ w hw horb' hx i hi
    have hx0Q : (0 : ℚ) < x₀ := by exact_mod_cast hx0
    have hphi0 : 0 < phi w := by
      by_contra h
      push Not at h
      have h0 : phi w = 0 := by omega
      rw [h0] at hx
      simp at hx
      linarith
    have htrue : true ∈ w := (phi_pos_iff w).mp hphi0
    have hdpos : 0 < d w := by
      have hpq : (0 : ℚ) < phi w := by exact_mod_cast hphi0
      have h : (0 : ℚ) < d w := by
        by_contra h
        push Not at h
        have : (phi w : ℚ) / (d w : ℚ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hpq.le h
        linarith
      exact_mod_cast h
    have hdvd : d w ∣ (phi w : ℤ) := by
      refine ⟨x₀, ?_⟩
      have hdq : (d w : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
      have h : ((phi w : ℕ) : ℚ) = (d w : ℚ) * (x₀ : ℚ) := by rw [hx, mul_div_cancel₀ _ hdq]
      exact_mod_cast h
    refine ⟨w, ?_, ?_, ?_⟩
    · by_contra h3
      push Not at h3
      clear_value w
      clear horb' hpt
      rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, w'⟩⟩⟩⟩
      · exact hw rfl
      all_goals (try (simp only [List.length_cons] at h3; omega))
      all_goals (try (cases a)) <;> (try (cases b)) <;> (try (cases c))
      all_goals first
        | (exfalso; revert hphi0 hdpos hdvd; decide)
        | (apply hne
           have hx' := hx
           norm_num [phi, phiRev, LaboBP.d] at hx'
           first
             | (rw [hx']; exact cycle_one)
             | (rw [hx']; exact cycle_two)
             | (subst hx'; simpa using cycle_one)
             | (subst hx'; simpa using cycle_two))
    · intro k hk0 hkl hrot
      have hk : collatzQ^[k] (x₀ : ℚ) = x₀ := by rw [hpt k hkl.le, hrot, ← hx]
      have := Function.IsPeriodicPt.minimalPeriod_le hk0 hk
      rw [hwl] at hkl
      omega
    · rw [lemma9_15_gen_thm w htrue, gcd_eq_right_iff _ _ (Int.normalize_of_nonneg hdpos.le)]
      exact hdvd
  · rintro ⟨s, hl3, hnp, hg⟩
    have hs : s ≠ [] := by intro h; simp [h] at hl3
    have hd0 : d s ≠ 0 := d_ne_zero s hs
    have htrue : true ∈ s := by
      by_contra h
      apply hd0
      rw [← hg]
      apply Finset.gcd_eq_zero_iff.mpr
      intro k _
      have h0 : phi (s.rotate (k + 1)) = 0 := by
        by_contra h0
        exact h (List.mem_rotate.mp ((phi_pos_iff _).mp (Nat.pos_of_ne_zero h0)))
      simp [h0]
    have hg2 : GCDMonoid.gcd (phi s : ℤ) (d s) = d s := by rw [← lemma9_15_gen_thm s htrue]; exact hg
    have hdnn : 0 ≤ d s := by
      rw [← hg2]
      exact Int.nonneg_of_normalize_eq_self (normalize_gcd _ _)
    have hdpos : 0 < d s := lt_of_le_of_ne hdnn (Ne.symm hd0)
    have hdvd : d s ∣ (phi s : ℤ) := by rw [← hg2]; exact gcd_dvd_left _ _
    obtain ⟨q, hq⟩ := hdvd
    have hphi0 : 0 < phi s := (phi_pos_iff s).mpr htrue
    have hq0 : 0 < q := by
      by_contra h
      push Not at h
      have h1 : d s * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdpos.le h
      have h2 : (0 : ℤ) < phi s := by exact_mod_cast hphi0
      linarith
    have hxq : ((q.toNat : ℕ) : ℚ) = (phi s : ℚ) / (d s : ℚ) := by
      have hdq : (d s : ℚ) ≠ 0 := by exact_mod_cast hd0
      rw [eq_div_iff hdq]
      have hqn : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0.le
      have h : (((q.toNat : ℕ) : ℤ) : ℚ) * ((d s : ℤ) : ℚ) = (((phi s : ℕ) : ℤ) : ℚ) := by
        rw [hqn, hq]; push_cast; ring
      exact_mod_cast h
    obtain ⟨hDodd, -, horb, hcyc⟩ := lemma2_cycle_thm s hs
    have hperQ : ((q.toNat : ℕ) : ℚ) ∈ Function.periodicPts collatzQ :=
      ⟨s.length, by omega, by show collatzQ^[s.length] _ = _; rw [hxq]; exact hcyc⟩
    refine ⟨q.toNat, by omega, hperQ, ?_⟩
    intro hC
    -- the minimal period is `l`, by non-periodicity of `s`
    set x0 : ℚ := (phi s : ℚ) / (d s : ℚ) with hx0def
    have hperx : Function.IsPeriodicPt collatzQ s.length x0 := hcyc
    set p := Function.minimalPeriod collatzQ x0 with hpdef
    have hpdvd : p ∣ s.length := hperx.minimalPeriod_dvd
    have hppos : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts ⟨s.length, by omega, hcyc⟩
    have hpar : ∀ j, j < s.length → ((collatzQ^[j] x0).num % 2 = 0 ↔ s[j]! = false) := by
      intro j hj
      rw [(horb j hj.le).1, orbit_formula s hs j hj.le]
      have h1 := (num_parity (phi (s.rotate j)) (d s) hDodd).1
      have h2 := phi_rot_parity s j hj
      push_cast at h1
      rw [h1, h2, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simp
    have hpl : p = s.length := by
      by_contra hne
      have hplt : p < s.length := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpdvd) hne
      apply hnp p hppos hplt
      apply List.ext_getElem (by simp)
      intro i h1 h2
      rw [List.getElem_rotate]
      have hm : (i + p) % s.length < s.length := Nat.mod_lt _ (by omega)
      have heq : collatzQ^[(i + p) % s.length] x0 = collatzQ^[i] x0 := by
        rw [hperx.iterate_mod_apply, Function.iterate_add_apply, Function.iterate_minimalPeriod]
      have a1 := hpar _ hm
      have a2 := hpar i h2
      rw [heq] at a1
      have e1 : s[(i + p) % s.length]! = s[(i + p) % s.length] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hm]; rfl
      have e2 : s[i]! = s[i] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
      rw [e1] at a1
      rw [e2] at a2
      cases hb1 : s[(i + p) % s.length] <;> cases hb2 : s[i] <;> simp_all
    have hcard := cycle_ncard _ hperQ
    rw [hC, Set.ncard_pair (by norm_num)] at hcard
    have : Function.minimalPeriod collatzQ ((q.toNat : ℕ) : ℚ) = p := by rw [hxq]
    omega

end LaboHH
