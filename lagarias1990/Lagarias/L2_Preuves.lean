import Mathlib
import Lagarias.L1990_Enonces

/-!
# Lagarias 1990 · Section 2 · proofs

Theorem 2.1, (2.1), (1.3), Corollary 2.1a (two proofs), the denominator facts of p. 39, the dichotomy of p. 37,
the injectivity of the parity map (p. 38, cited by Lagarias from [10], proved here), Corollary 2.1b.
Statements: `Lagarias/L1990_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP LaboHH

/-! ## Basics -/

lemma xv_eq_phi (v : List Bool) : xv v = (phi v : ℚ) / (d v : ℚ) := by
  simp [xv, phi_eq_C_thm v]

lemma d_cast (v : List Bool) : ((d v : ℤ) : ℚ) = (2 : ℚ) ^ v.length - 3 ^ v.count true := by
  simp [LaboBP.d]

lemma d_odd (v : List Bool) (hv : v ≠ []) : Odd (d v) := (lemma2_cycle_thm v hv).1

lemma par_eq (x : ℚ) : collatzQ x = gStep (par x) x := by
  unfold collatzQ gStep par
  rcases Int.emod_two_eq_zero_or_one x.num with h | h <;> simp [h]

lemma parWord_length (x : ℚ) (n : ℕ) : (parWord x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [parWord, ih]

lemma parWord_getElem (x : ℚ) (n i : ℕ) (hi : i < (parWord x n).length) :
    (parWord x n)[i] = par (collatzQ^[i] x) := by
  induction n generalizing x i with
  | zero => simp [parWord] at hi
  | succ n ih =>
    cases i with
    | zero => simp [parWord]
    | succ i =>
      simp only [parWord, List.getElem_cons_succ]
      rw [ih]
      rfl

lemma parWord_eq_iff (x : ℚ) (v : List Bool) :
    parWord x v.length = v ↔ ∀ i (hi : i < v.length), par (collatzQ^[i] x) = v[i] := by
  constructor
  · intro h i hi
    have hi' : i < (parWord x v.length).length := by rw [parWord_length]; exact hi
    rw [← parWord_getElem x v.length i hi']
    simp [h]
  · intro h
    apply List.ext_getElem (by rw [parWord_length])
    intro i h1 h2
    rw [parWord_getElem, h i h2]

/-- Following the parity word: the orbit is `phiMap` of the prefixes. -/
lemma orbit_of_parity (y : ℚ) (v : List Bool)
    (hpar : ∀ i (hi : i < v.length), par (collatzQ^[i] y) = v[i]) :
    ∀ i, i ≤ v.length → collatzQ^[i] y = phiMap (v.take i) y := by
  intro i
  induction i with
  | zero => intro _; simp [phiMap_nil]
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega), List.take_succ_eq_append_getElem (by omega),
      phiMap_append_singleton, par_eq, ← ih (by omega), hpar i (by omega)]

/-! ## Theorem 2.1 and (2.1) -/

theorem thm2_1_thm : thm2_1 := by
  intro v hv
  obtain ⟨hDodd, hden, hiter, hper⟩ := lemma2_cycle_thm v hv
  rw [xv_eq_phi]
  refine ⟨hden, hper, ?_, ?_⟩
  · rw [parWord_eq_iff]
    intro i hi
    rw [(hiter i hi.le).1, orbit_formula v hv i hi.le]
    have hp := (num_parity (phi (v.rotate i)) (d v) hDodd).1
    have hr := phi_rot_parity v i hi
    unfold par
    rcases Int.emod_two_eq_zero_or_one (((phi (v.rotate i) : ℤ) : ℚ) / (d v : ℚ)).num with h | h
    · have h1 : ((phi (v.rotate i) : ℕ) : ℤ) % 2 = 0 := by
        have := hp.mp (by exact_mod_cast h)
        exact_mod_cast this
      have h2 := hr.mp h1
      simp only [Int.cast_natCast] at h
      simp [h, h2]
    · have h1 : ¬ ((phi (v.rotate i) : ℕ) : ℤ) % 2 = 0 := by
        intro h0
        have := hp.mpr h0
        simp only [Int.cast_natCast] at this h
        omega
      have h2 : v[i] = true := by
        cases hb : v[i]
        · exact absurd (hr.mpr hb) h1
        · rfl
      simp only [Int.cast_natCast] at h
      simp [h, h2]
  · intro y _ hy hpw
    have horb := orbit_of_parity y v ((parWord_eq_iff y v).mp hpw) v.length le_rfl
    rw [List.take_length] at horb
    have hfix := (lemma2_fixed_thm ℚ v hv).2 y
    rw [← d_cast] at hfix
    exact hfix.mp (horb ▸ hy)

theorem eq2_1_thm : eq2_1 := by
  intro v
  rw [xv, C_eq_Csum v, d_cast, div_eq_inv_mul]
  congr 1
  unfold Csum
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-! ## Exponent lists: (1.3) -/

/-- Positions of the ones of a word, in decreasing order. -/
def pos : List Bool → List ℕ
  | [] => []
  | b :: w => (pos w).map (· + 1) ++ (if b then [0] else [])

lemma S3_append (L L' : List ℕ) : S3 (L ++ L') = S3 L + 3 ^ L.length * S3 L' := by
  induction L with
  | nil => simp [S3]
  | cons a L ih => simp [S3, ih, pow_succ]; ring

lemma S3_map_succ (L : List ℕ) : S3 (L.map (· + 1)) = 2 * S3 L := by
  induction L with
  | nil => simp [S3]
  | cons a L ih => simp [S3, ih, pow_succ]; ring

lemma pos_length (v : List Bool) : (pos v).length = v.count true := by
  induction v with
  | nil => rfl
  | cons b w ih => cases b <;> simp [pos, ih]

lemma pos_lt (v : List Bool) : ∀ a ∈ pos v, a < v.length := by
  induction v with
  | nil => simp [pos]
  | cons b w ih =>
    intro a ha
    simp only [pos, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨c, hc, rfl⟩ | ha
    · simp [ih c hc]
    · cases b <;> simp_all

lemma pos_sorted (v : List Bool) : (pos v).Pairwise (· > ·) := by
  induction v with
  | nil => simp [pos]
  | cons b w ih =>
    simp only [pos]
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]; exact ih.imp (fun h => by omega)
    · cases b <;> simp
    · intro a ha c hc
      simp only [List.mem_map] at ha
      obtain ⟨a', _, rfl⟩ := ha
      cases b <;> simp_all

lemma C_eq_S3_pos (v : List Bool) : C v = S3 (pos v) := by
  induction v with
  | nil => rfl
  | cons b w ih =>
    simp only [pos, S3_append, S3_map_succ, List.length_map, pos_length, ← ih]
    cases b <;> simp [C, S3]; ring

/-- A strictly decreasing list with `0` in it ends with `0`. -/
lemma filter_zero (L : List ℕ) (hL : L.Pairwise (· > ·)) :
    L.filter (· ≠ 0) ++ (if 0 ∈ L then [0] else []) = L := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    by_cases ha : a = 0
    · subst ha
      have hL0 : L = [] := by
        rcases L with _ | ⟨b, L⟩
        · rfl
        · exact absurd (hL.1 b (by simp)) (by omega)
      subst hL0
      simp
    · have h0 : (0 ∈ a :: L) ↔ (0 ∈ L) := by simp [Ne.symm ha]
      simp only [List.filter_cons, ha, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
        List.cons_append]
      rw [show (if 0 ∈ a :: L then [0] else []) = (if 0 ∈ L then [0] else []) by simp [h0]]
      rw [ih hL.2]

lemma exists_pos (n : ℕ) : ∀ L : List ℕ, L.Pairwise (· > ·) → (∀ a ∈ L, a < n) →
    ∃ v : List Bool, v.length = n ∧ pos v = L := by
  induction n with
  | zero =>
    intro L _ hb
    refine ⟨[], rfl, ?_⟩
    rcases L with _ | ⟨a, L⟩
    · rfl
    · exact absurd (hb a (by simp)) (by omega)
  | succ n ih =>
    intro L hL hb
    set L' := (L.filter (· ≠ 0)).map (· - 1) with hL'
    have hL's : L'.Pairwise (· > ·) := by
      rw [hL', List.pairwise_map]
      refine (hL.filter _).imp_of_mem fun {a b} ha hb' hab => ?_
      simp only [List.mem_filter, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not] at ha hb'
      omega
    have hL'b : ∀ a ∈ L', a < n := by
      intro a ha
      rw [hL', List.mem_map] at ha
      obtain ⟨c, hc, rfl⟩ := ha
      rw [List.mem_filter] at hc
      have := hb c hc.1
      have hc0 : c ≠ 0 := by simpa using hc.2
      omega
    obtain ⟨w, hw, hpw⟩ := ih L' hL's hL'b
    refine ⟨decide (0 ∈ L) :: w, by simp [hw], ?_⟩
    simp only [pos, hpw, hL', List.map_map]
    have hmap : (L.filter (· ≠ 0)).map ((· + 1) ∘ (· - 1)) = L.filter (· ≠ 0) := by
      conv_rhs => rw [← List.map_id (L.filter (· ≠ 0))]
      refine List.map_congr_left fun a ha => ?_
      rw [List.mem_filter] at ha
      simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at ha
      simp only [Function.comp_apply, id_eq]
      omega
    rw [hmap]
    conv_rhs => rw [← filter_zero L hL]
    by_cases h0 : 0 ∈ L <;> simp [h0]

lemma xv_eq_S3 (v : List Bool) :
    xv v = (S3 (pos v) : ℚ) / ((2 : ℚ) ^ v.length - 3 ^ (pos v).length) := by
  rw [xv, C_eq_S3_pos, d_cast, pos_length]

theorem eq1_3_thm : eq1_3 := by
  refine ⟨fun v _ => ⟨pos v, pos_sorted v, pos_length v, pos_lt v, xv_eq_S3 v⟩, ?_⟩
  intro n L _ hL hb
  obtain ⟨v, hv, hpv⟩ := exists_pos n L hL hb
  exact ⟨v, hv, by rw [xv_eq_S3, hpv, hv]⟩

/-! ## Corollary 2.1a -/

lemma C_mod_two (b : Bool) (w : List Bool) : C (b :: w) % 2 = if b then 1 else 0 := by
  have h3 : 3 ^ w.count true % 2 = 1 := by rw [Nat.pow_mod]; simp
  cases b <;> simp [C] <;> omega

/-- Corollary 2.1a, word form: Coppersmith's argument (the lowest bit is read off modulo 2). -/
theorem cor2_1a_words_thm : cor2_1a_words := by
  intro v
  induction v with
  | nil => intro w hl _ _; exact (List.length_eq_zero_iff.mp hl.symm).symm
  | cons a v ih =>
    intro w hl hc hC
    rcases w with _ | ⟨b, w⟩
    · simp at hl
    have hab : a = b := by
      have := C_mod_two a v
      rw [hC, C_mod_two b w] at this
      cases a <;> cases b <;> simp_all
    subst hab
    have hc' : v.count true = w.count true := by
      cases a <;> simpa [List.count_cons] using hc
    have hC' : C v = C w := by
      cases a <;> simp [C, hc'] at hC <;> omega
    rw [ih w (by simpa using hl) hc' hC']

/-- Corollary 2.1a, Coppersmith's proof (through the word form). -/
theorem cor2_1a_coppersmith : cor2_1a := by
  intro L L' hl hL hL' hS
  obtain ⟨n, hn⟩ : ∃ n, n = (L ++ L').sum + 1 := ⟨_, rfl⟩
  have hb : ∀ a ∈ L ++ L', a < n := by
    intro a ha
    have : a ≤ (L ++ L').sum := List.le_sum_of_mem ha
    omega
  obtain ⟨v, hv, hpv⟩ := exists_pos n L hL fun a ha => hb a (List.mem_append_left _ ha)
  obtain ⟨w, hw, hpw⟩ := exists_pos n L' hL' fun a ha => hb a (List.mem_append_right _ ha)
  have hc : v.count true = w.count true := by rw [← pos_length, ← pos_length, hpv, hpw, hl]
  have hC : C v = C w := by rw [C_eq_S3_pos, C_eq_S3_pos, hpv, hpw, hS]
  rw [← hpv, ← hpw, cor2_1a_words_thm v w (hv.trans hw.symm) hc hC]

/-- Corollary 2.1a, Lagarias's proof (through Theorem 2.1). -/
theorem cor2_1a_lagarias : cor2_1a := by
  intro L L' hl hL hL' hS
  obtain ⟨n, hn⟩ : ∃ n, n = (L ++ L').sum + 1 := ⟨_, rfl⟩
  have hb : ∀ a ∈ L ++ L', a < n := by
    intro a ha
    have : a ≤ (L ++ L').sum := List.le_sum_of_mem ha
    omega
  obtain ⟨v, hv, hpv⟩ := exists_pos n L hL fun a ha => hb a (List.mem_append_left _ ha)
  obtain ⟨w, hw, hpw⟩ := exists_pos n L' hL' fun a ha => hb a (List.mem_append_right _ ha)
  have hvne : v ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hx : xv v = xv w := by rw [xv_eq_S3, xv_eq_S3, hpv, hpw, hS, hl, hv, hw]
  have h1 := (thm2_1_thm v hvne).2.2.1
  have h2 := (thm2_1_thm w hwne).2.2.1
  rw [hv] at h1
  rw [hw, ← hx] at h2
  rw [← hpv, ← hpw, ← h1, h2]

theorem ex_p37_thm : ex_p37 := ⟨rfl, rfl⟩

/-! ## Denominators (p. 39) -/

lemma den_div_dvd (a D : ℤ) : (((a : ℚ) / D).den : ℤ) ∣ D := by
  have := Rat.den_dvd a D
  rwa [Rat.divInt_eq_div] at this

lemma den_one_third : (1 / 3 : ℚ).den = 3 := by decide +kernel

theorem den_step_thm : den_step := by
  intro x hx
  obtain ⟨p, hp⟩ : ∃ p, p = x.num := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = x.den := ⟨_, rfl⟩
  have hq0 : (q : ℚ) ≠ 0 := by rw [hq]; positivity
  have hx' : x = (p : ℚ) / ((q : ℕ) : ℤ) := by
    rw [hp, hq]; push_cast; exact (Rat.num_div_den x).symm
  have hqodd : Odd q := hq ▸ hx
  have hT : ∃ a : ℤ, collatzQ x = (a : ℚ) / ((q : ℕ) : ℤ) := by
    unfold collatzQ
    rw [← hp]
    split_ifs with h
    · refine ⟨p / 2, ?_⟩
      rw [hx']
      have e : (p : ℚ) = 2 * ((p / 2 : ℤ) : ℚ) := by
        exact_mod_cast (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h)).symm
      rw [e]; push_cast; field_simp
    · have hev : (2 : ℤ) ∣ 3 * p + q := by
        obtain ⟨t, ht⟩ := hqodd
        exact Int.dvd_of_emod_eq_zero (by omega)
      refine ⟨(3 * p + q) / 2, ?_⟩
      rw [hx']
      have e : ((3 * p + q : ℤ) : ℚ) = 2 * (((3 * p + q) / 2 : ℤ) : ℚ) := by
        exact_mod_cast (Int.mul_ediv_cancel' hev).symm
      rw [show (((3 * p + q) / 2 : ℤ) : ℚ) = ((3 * p + q : ℤ) : ℚ) / 2 by rw [e]; ring]
      push_cast; field_simp
  obtain ⟨a, ha⟩ := hT
  have hdvd : (collatzQ x).den ∣ q := by
    have := den_div_dvd a q
    rw [← ha] at this
    exact_mod_cast this
  refine ⟨Odd.of_dvd_nat hqodd hdvd, hq ▸ hdvd, fun h3 => ?_⟩
  apply Nat.dvd_antisymm (hq ▸ hdvd)
  have hy : collatzQ x = x / 2 ∨ collatzQ x = (3 * x + 1) / 2 := by
    unfold collatzQ; split_ifs <;> simp
  rcases hy with hy | hy
  · have e : x = 2 * collatzQ x := by rw [hy]; ring
    have h1 := Rat.mul_den_dvd 2 (collatzQ x)
    rw [← e] at h1
    simpa using h1
  · have e : x = (2 * collatzQ x - 1) * (1 / 3) := by rw [hy]; ring
    have h1 := Rat.mul_den_dvd (2 * collatzQ x - 1) (1 / 3)
    rw [← e, den_one_third] at h1
    have h2 : (2 * collatzQ x - 1).den ∣ (collatzQ x).den := by
      have h4 := Rat.sub_den_dvd (2 * collatzQ x) 1
      have h5 := Rat.mul_den_dvd 2 (collatzQ x)
      simp only [Rat.den_ofNat, mul_one, one_mul] at h4 h5
      exact h4.trans h5
    have h6 : x.den ∣ (collatzQ x).den * 3 := h1.trans (Nat.mul_dvd_mul_right h2 3)
    have hc : Nat.Coprime x.den 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
    exact hc.dvd_of_dvd_mul_right h6

theorem den_printed_false_thm : den_printed_false := by
  refine ⟨1 / 3, by rw [den_one_third]; decide, ?_⟩
  have : collatzQ (1 / 3) = 1 := by norm_num [collatzQ]
  rw [this, den_one_third]
  decide

lemma odd_den_iter (x : ℚ) (hx : Odd x.den) (j : ℕ) : Odd (collatzQ^[j] x).den := by
  induction j with
  | zero => exact hx
  | succ j ih => rw [Function.iterate_succ_apply']; exact (den_step_thm _ ih).1

lemma den_iter_dvd (x : ℚ) (hx : Odd x.den) (i j : ℕ) :
    (collatzQ^[j + i] x).den ∣ (collatzQ^[i] x).den := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show j + 1 + i = (j + i) + 1 by omega, Function.iterate_succ_apply']
    exact (den_step_thm _ (odd_den_iter x hx _)).2.1.trans ih

theorem den_cycle_thm : den_cycle := by
  intro x hx p hp hper j
  apply Nat.dvd_antisymm
  · simpa using den_iter_dvd x hx 0 j
  · have hper' : collatzQ^[p * (j + 1)] x = x := by
      have : Function.IsPeriodicPt collatzQ p x := hper
      exact (this.mul_const (j + 1)).eq
    have hle : j ≤ p * (j + 1) := by nlinarith
    have h := den_iter_dvd x hx j (p * (j + 1) - j)
    rw [show p * (j + 1) - j + j = p * (j + 1) by omega, hper'] at h
    exact h

lemma den_div_int (a b : ℤ) (hb : b ≠ 0) : (((a : ℚ) / b).den : ℤ) = |b| / (Int.gcd a b : ℤ) := by
  obtain ⟨g, a', b', hg, hcop, ha, hb'⟩ := Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_right a hb)
  have hgab : Int.gcd a b = g := by
    rw [ha, hb', Int.gcd_mul_right, hcop]; simp
  have hb'0 : b' ≠ 0 := by rintro rfl; simp at hb'; exact hb hb'
  have hg0 : (g : ℚ) ≠ 0 := by positivity
  have hq : (a : ℚ) / b = (a' : ℚ) / b' := by
    rw [ha, hb']; push_cast; field_simp
  have hcop' : Nat.Coprime a'.natAbs b'.natAbs := by
    exact hcop
  rw [hq, hgab, hb', abs_mul, Nat.abs_cast, Int.mul_ediv_cancel _ (by exact_mod_cast hg.ne')]
  rcases lt_or_gt_of_ne hb'0 with hneg | hpos
  · have e : (a' : ℚ) / b' = ((-a' : ℤ) : ℚ) / ((-b' : ℤ) : ℚ) := by push_cast; rw [neg_div_neg_eq]
    rw [e, Rat.den_div_eq_of_coprime (by omega) (by simpa using hcop'), abs_of_neg hneg]
  · rw [Rat.den_div_eq_of_coprime hpos hcop', abs_of_pos hpos]

theorem delta_eq_thm : delta_eq := by
  intro v hv
  have hd : d v ≠ 0 := d_ne_zero v hv
  rw [xv]
  have := den_div_int (C v) (d v) hd
  simpa using this

/-! ## The dichotomy of p. 37 -/

theorem dichotomy_thm : dichotomy := by
  intro x hx
  by_cases hdiv : Divergent x
  · exact Or.inr hdiv
  left
  have hanti : ∀ i j, i ≤ j → (collatzQ^[j] x).den ≤ (collatzQ^[i] x).den := fun i j hij => by
    have := den_iter_dvd x hx i (j - i)
    rw [show j - i + i = j by omega] at this
    exact Nat.le_of_dvd (Rat.den_pos _) this
  obtain ⟨N, hN⟩ : ∃ N, ∀ j, N ≤ j → (collatzQ^[j] x).den = (collatzQ^[N] x).den := by
    obtain ⟨N, hNm⟩ := Nat.sInf_mem (Set.range_nonempty fun j => (collatzQ^[j] x).den)
    refine ⟨N, fun j hj => le_antisymm (hanti N j hj) ?_⟩
    have hNm' : (collatzQ^[N] x).den = sInf (Set.range fun j => (collatzQ^[j] x).den) := hNm
    rw [hNm']
    exact Nat.sInf_le ⟨j, rfl⟩
  unfold Divergent at hdiv
  rw [Filter.tendsto_atTop_atTop] at hdiv
  push Not at hdiv
  obtain ⟨B, hB⟩ := hdiv
  set q := (collatzQ^[N] x).den with hq
  have hs : {j | N ≤ j ∧ |collatzQ^[j] x| < B}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    obtain ⟨a, ha, hab⟩ := hB (max M N + 1)
    have := hM (show a ∈ {j | N ≤ j ∧ |collatzQ^[j] x| < B} from ⟨by omega, hab⟩)
    omega
  have ht : {y : ℚ | y.den = q ∧ |y| < B}.Finite := by
    apply ((Set.finite_Icc (-⌈B * q⌉) ⌈B * q⌉).image (fun a : ℤ => (a : ℚ) / (q : ℚ))).subset
    rintro y ⟨hy1, hy2⟩
    have hq0 : (0 : ℚ) < y.den := by positivity
    have hyq : (y.den : ℚ) = q := by exact_mod_cast hy1
    have e : (y.num : ℚ) = y * y.den := (Rat.mul_den_eq_num y).symm
    have habs : |(y.num : ℚ)| < B * q := by
      rw [e, abs_mul, abs_of_pos hq0, ← hyq]
      exact mul_lt_mul_of_pos_right hy2 hq0
    have hc := Int.le_ceil (B * q)
    rw [abs_lt] at habs
    refine ⟨y.num, ⟨?_, ?_⟩, ?_⟩
    · have : (-(⌈B * q⌉ : ℚ)) ≤ (y.num : ℚ) := by linarith
      exact_mod_cast this
    · have : (y.num : ℚ) ≤ ⌈B * q⌉ := by linarith
      exact_mod_cast this
    · show (y.num : ℚ) / (q : ℚ) = y
      rw [← hyq]
      exact Rat.num_div_den y
  have hmaps : Set.MapsTo (fun j => collatzQ^[j] x) {j | N ≤ j ∧ |collatzQ^[j] x| < B}
      {y : ℚ | y.den = q ∧ |y| < B} := fun j hj => ⟨hN j hj.1, hj.2⟩
  obtain ⟨j1, hj1, j2, hj2, hne, heq⟩ := hs.exists_ne_map_eq_of_mapsTo hmaps ht
  have key : ∀ a b : ℕ, a < b → collatzQ^[a] x = collatzQ^[b] x → EvPeriodic (fun j => collatzQ^[j] x) :=
    fun a b hab he => ⟨a, b - a, by omega, fun j hj => by
      simp only
      rw [show j + (b - a) = (j - a) + b by omega, Function.iterate_add_apply, ← he,
        ← Function.iterate_add_apply, show j - a + a = j by omega]⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact key j1 j2 h heq
  · exact key j2 j1 h heq.symm

/-! ## Injectivity of the parity map (p. 38) -/

lemma diff_iter (x y : ℚ) (h : bseq x = bseq y) :
    ∀ j, ∃ c : ℕ, (collatzQ^[j] x - collatzQ^[j] y) * 2 ^ j = 3 ^ c * (x - y) := by
  intro j
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    have hp : par (collatzQ^[j] x) = par (collatzQ^[j] y) := congrFun h j
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', par_eq (collatzQ^[j] x),
      par_eq (collatzQ^[j] y), ← hp]
    cases par (collatzQ^[j] x)
    · refine ⟨c, ?_⟩
      simp only [gStep, Bool.false_eq_true, ↓reduceIte]
      rw [← hc]; ring
    · refine ⟨c + 1, ?_⟩
      simp only [gStep, ↓reduceIte]
      have e : ((3 * collatzQ^[j] x + 1) / 2 - (3 * collatzQ^[j] y + 1) / 2) * 2 ^ (j + 1)
          = 3 * ((collatzQ^[j] x - collatzQ^[j] y) * 2 ^ j) := by ring
      rw [e, hc]; ring

theorem bseq_inj_thm : bseq_inj := by
  intro x y hx hy h
  by_contra hne
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = x - y := ⟨_, rfl⟩
  have hδ0 : δ ≠ 0 := by rw [hδ]; exact sub_ne_zero.mpr hne
  have hnum0 : δ.num ≠ 0 := Rat.num_ne_zero.mpr hδ0
  obtain ⟨c, hc⟩ := diff_iter x y h δ.num.natAbs
  obtain ⟨j, hj⟩ : ∃ j, j = δ.num.natAbs := ⟨_, rfl⟩
  rw [← hj, ← hδ] at hc
  obtain ⟨r, hr⟩ : ∃ r, r = collatzQ^[j] x - collatzQ^[j] y := ⟨_, rfl⟩
  rw [← hr] at hc
  have hrodd : Odd r.den := by
    rw [hr]
    exact Odd.of_dvd_nat (Odd.mul (odd_den_iter x hx j) (odd_den_iter y hy j)) (Rat.sub_den_dvd _ _)
  have key : (r.num : ℚ) * 2 ^ j * δ.den = 3 ^ c * δ.num * r.den := by
    have e1 := Rat.num_div_den r
    have e2 := Rat.num_div_den δ
    have hrd : (r.den : ℚ) ≠ 0 := by positivity
    have hdd : (δ.den : ℚ) ≠ 0 := by positivity
    rw [← e1, ← e2] at hc
    field_simp at hc
    linear_combination hc
  have key' : r.num * 2 ^ j * δ.den = 3 ^ c * δ.num * r.den := by exact_mod_cast key
  have hdvd : (2 : ℤ) ^ j ∣ 3 ^ c * δ.num * r.den := ⟨r.num * δ.den, by rw [← key']; ring⟩
  have hnat : 2 ^ j ∣ δ.num.natAbs * (3 ^ c * r.den) := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at this
    rw [show δ.num.natAbs * (3 ^ c * r.den) = 3 ^ c * δ.num.natAbs * r.den by ring]
    exact this
  have hcop : Nat.Coprime (2 ^ j) (3 ^ c * r.den) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact Odd.mul (Odd.pow (by decide)) hrodd
  have h2 : 2 ^ j ∣ δ.num.natAbs := hcop.dvd_of_dvd_mul_right hnat
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hnum0) h2
  rw [← hj] at hle
  exact absurd hle (not_le.mpr j.lt_two_pow_self)

/-! ## Corollary 2.1b -/

lemma bseq_add (x : ℚ) (N j : ℕ) : bseq (collatzQ^[N] x) j = bseq x (j + N) := by
  simp [bseq, Function.iterate_add_apply]

lemma bseq_periodic (z : ℚ) (p : ℕ) (hz : collatzQ^[p] z = z) (j : ℕ) :
    bseq z (j + p) = bseq z j := by
  simp [bseq, Function.iterate_add_apply, hz]

theorem cor2_1b_thm : cor2_1b := by
  intro x hx hdiv hev
  obtain ⟨N, p, hp, hper⟩ := hev
  obtain ⟨y, hy⟩ : ∃ y, y = collatzQ^[N] x := ⟨_, rfl⟩
  have hyodd : Odd y.den := hy ▸ odd_den_iter x hx N
  have hyper : ∀ j, bseq y (j + p) = bseq y j := by
    intro j
    rw [hy, bseq_add, bseq_add, show j + p + N = (j + N) + p by omega]
    exact hper (j + N) (by omega)
  obtain ⟨v, hv⟩ : ∃ v, v = parWord y p := ⟨_, rfl⟩
  have hvl : v.length = p := by rw [hv, parWord_length]
  have hvne : v ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨hzodd, hzper, hzpar, -⟩ := thm2_1_thm v hvne
  have hypar : parWord y v.length = v := by rw [hvl, hv]
  rw [hvl] at hzper
  have hb : bseq (xv v) = bseq y := by
    funext j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hj : j < p
      · have hj' : j < v.length := by omega
        rw [bseq, bseq, (parWord_eq_iff _ v).mp hzpar j hj', (parWord_eq_iff _ v).mp hypar j hj']
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + p := ⟨j - p, by omega⟩
        rw [bseq_periodic _ p hzper, hyper i, ih i (by omega)]
  have hzy : xv v = y := bseq_inj_thm _ _ hzodd hyodd hb
  have hyp : collatzQ^[p] y = y := by rw [← hzy]; exact hzper
  rw [Divergent, Filter.tendsto_atTop_atTop] at hdiv
  obtain ⟨M, hM⟩ := hdiv (|y| + 1)
  have hk : collatzQ^[p * M + N] x = y := by
    rw [Function.iterate_add_apply, ← hy]
    exact (Function.IsPeriodicPt.mul_const (show Function.IsPeriodicPt collatzQ p y from hyp) M).eq
  have h1 := hM (p * M + N) (by nlinarith)
  rw [hk] at h1
  linarith

end Lagarias
