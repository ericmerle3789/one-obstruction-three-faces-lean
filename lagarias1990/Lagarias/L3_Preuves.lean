import Mathlib
import Lagarias.L2_Preuves

/-!
# Lagarias 1990 · Section 3 · proofs (phase 2a)

The `3x+k` functions, clearing denominators, the repaired statements of p. 40 (sign, `3 ∤ k`), the bijection
between rational cycles and primitive cycles, the unproved remark of p. 44 (`n0 ≡ ±1 (mod 6)`),
Theorem 3.4, (3.8), Theorem 3.5, and the examples of pp. 44–45.
Statements: `Lagarias/L1990_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP LaboHH

/-! ## Elementary facts on `T_k` -/

lemma Tk_even {k n : ℤ} (h : n % 2 = 0) : Tk k n = n / 2 := by simp [Tk, h]

lemma Tk_odd {k n : ℤ} (h : n % 2 = 1) : Tk k n = (3 * n + k) / 2 := by simp [Tk, h]

lemma two_mul_Tk {k n : ℤ} (hk : Odd k) : 2 * Tk k n = if n % 2 = 0 then n else 3 * n + k := by
  obtain ⟨t, rfl⟩ := hk
  unfold Tk
  split_ifs with h <;> omega

lemma coprime_two_of_dvd_odd {e k : ℤ} (he : e ∣ k) (hk : Odd k) : IsCoprime e 2 := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  obtain ⟨c, rfl⟩ := he
  have : Odd e := (Int.odd_mul.mp hk).1
  have h2 : Nat.Coprime e.natAbs 2 := Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr this)
  exact h2

lemma coprime_three_of_dvd {e k : ℤ} (he : e ∣ k) (h3 : ¬ (3 : ℤ) ∣ k) : IsCoprime e 3 := by
  apply IsCoprime.symm
  rw [Prime.coprime_iff_not_dvd Int.prime_three]
  exact fun h => h3 (h.trans he)

/-- One step of `T` on `m/k` is one step of `T_k` on `m`. -/
lemma collatzQ_div (k m : ℤ) (hk0 : 0 < k) (hk : Odd k) :
    collatzQ ((m : ℚ) / k) = ((Tk k m : ℤ) : ℚ) / k := by
  have hk0' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  rw [collatzQ_eq ((m : ℚ) / k) m k hk rfl (decide (m % 2 = 1)) (by
    rcases Int.emod_two_eq_zero_or_one m with h | h <;> simp [h])]
  unfold gStep Tk
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · have e : ((m / 2 : ℤ) : ℚ) = (m : ℚ) / 2 := by
      rw [Int.cast_div (Int.dvd_of_emod_eq_zero h) (by norm_num)]; norm_num
    rw [show decide (m % 2 = 1) = false by simp [h]]
    simp only [Bool.false_eq_true, ↓reduceIte, h, e]
    field_simp
  · have hev : (2 : ℤ) ∣ 3 * m + k := by
      obtain ⟨t, rfl⟩ := hk; exact Int.dvd_of_emod_eq_zero (by omega)
    have e : (((3 * m + k) / 2 : ℤ) : ℚ) = (3 * (m : ℚ) + k) / 2 := by
      rw [Int.cast_div hev (by norm_num)]; push_cast; ring
    rw [show decide (m % 2 = 1) = true by simp [h]]
    simp only [↓reduceIte, h, e, one_ne_zero]
    field_simp

theorem clear_den_thm : clear_den := by
  intro k m hk0 hk j
  have hk0' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  induction j generalizing m with
  | zero => simp; field_simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, collatzQ_div k m hk0 hk, ih, Function.iterate_succ_apply]

/-! ## The printed statements of p. 40, and their repairs -/

theorem D6_printed_false_thm : D6_printed_false := ⟨[false, false], by simp, by decide⟩

theorem D6_thm : D6 := by
  intro v hv
  have hvne : v ≠ [] := List.ne_nil_of_mem hv
  have hodd : Odd (d v) := d_odd v hvne
  have hl : 0 < v.count true := List.count_pos_iff.mpr hv
  have h3 : ¬ (3 : ℤ) ∣ d v := by
    intro h
    have h3l : (3 : ℤ) ∣ 3 ^ v.count true := dvd_pow_self 3 hl.ne'
    have h2 : (3 : ℤ) ∣ 2 ^ v.length := by
      have : (2 : ℤ) ^ v.length = d v + 3 ^ v.count true := by simp [LaboBP.d]
      rw [this]; exact dvd_add h h3l
    have := Int.prime_three.dvd_of_dvd_pow h2
    norm_num at this
  have c2 : Nat.Coprime (d v).natAbs 2 := Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hodd)
  have c3 : Nat.Coprime (d v).natAbs 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h; exact h3 (Int.ofNat_dvd_left.mpr h)
  have : Nat.Coprime (d v).natAbs (2 * 3) := Nat.Coprime.mul_right c2 c3
  exact this

theorem tk_sign_printed_false_thm : tk_sign_printed_false := ⟨1, 1, odd_one, by decide⟩

theorem tk_sign_thm : tk_sign := by
  intro k n hk
  obtain ⟨t, rfl⟩ := hk
  unfold Tk
  split_ifs with h1 h2 h2 <;> omega

theorem tk_Z_printed_false_thm : tk_Z_printed_false := ⟨9, 1, by decide, by decide⟩

theorem tk_Z_thm : tk_Z := by
  intro k n hk h3
  apply gcd_congr_right
  intro e he
  have c2 := coprime_two_of_dvd_odd he hk
  have h2T := two_mul_Tk (n := n) hk
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · rw [if_pos h] at h2T
    constructor
    · intro hT; rw [← h2T]; exact dvd_mul_of_dvd_right hT 2
    · intro hn; rw [← h2T] at hn; exact c2.dvd_of_dvd_mul_left hn
  · rw [if_neg (by omega)] at h2T
    have c3 := coprime_three_of_dvd he h3
    constructor
    · intro hT
      have : e ∣ 3 * n + k := by rw [← h2T]; exact dvd_mul_of_dvd_right hT 2
      have : e ∣ 3 * n := by simpa using dvd_sub this he
      exact c3.dvd_of_dvd_mul_left this
    · intro hn
      have : e ∣ 2 * Tk k n := by rw [h2T]; exact dvd_add (dvd_mul_of_dvd_right hn 3) he
      exact c2.dvd_of_dvd_mul_left this

theorem tk_scale_thm : tk_scale := by
  intro e k n he hk
  obtain ⟨a, rfl⟩ := he
  unfold Tk
  have hpar : ((2 * a + 1) * n) % 2 = n % 2 := by
    rw [Int.mul_emod, show (2 * a + 1) % 2 = 1 by omega, one_mul, Int.emod_emod_of_dvd _ (by norm_num)]
  rw [hpar]
  split_ifs with h
  · rw [Int.mul_ediv_assoc _ (Int.dvd_of_emod_eq_zero h)]
  · have hev : (2 : ℤ) ∣ 3 * n + k := by
      obtain ⟨t, rfl⟩ := hk; exact Int.dvd_of_emod_eq_zero (by omega)
    rw [show 3 * ((2 * a + 1) * n) + (2 * a + 1) * k = (2 * a + 1) * (3 * n + k) by ring,
      Int.mul_ediv_assoc _ hev]

/-! ## From primitive cycles to rational cycles, and back -/

/-- A periodic point of `T` in `Q_(2)` is `x(v)` for its own parity word. -/
lemma periodic_eq_xv (x : ℚ) (hx : Odd x.den) (p : ℕ) (hp : 0 < p) (hper : collatzQ^[p] x = x) :
    parWord x p ≠ [] ∧ (parWord x p).length = p ∧ x = xv (parWord x p) := by
  have hl : (parWord x p).length = p := parWord_length x p
  have hne : parWord x p ≠ [] := List.ne_nil_of_length_pos (by omega)
  refine ⟨hne, hl, ?_⟩
  exact (thm2_1_thm _ hne).2.2.2 x hx (by rw [hl]; exact hper) (by rw [hl])

lemma den_num_div (k m : ℤ) (hk0 : 0 < k) (hg : Int.gcd m k = 1) :
    ((m : ℚ) / k).den = k.toNat ∧ ((m : ℚ) / k).num = m := by
  have hc : Nat.Coprime m.natAbs k.natAbs := hg
  refine ⟨?_, Rat.num_div_eq_of_coprime hk0 hc⟩
  have := Rat.den_div_eq_of_coprime hk0 hc
  omega

/-- A member of a primitive cycle of `T_k` (`k > 0`) gives a periodic point `m/k ∈ Q_(2)`. -/
lemma prim_to_rat (k m : ℤ) (hk0 : 0 < k) (h : InPrimCycle k m) :
    ∃ p, 0 < p ∧ collatzQ^[p] ((m : ℚ) / k) = (m : ℚ) / k ∧ Odd ((m : ℚ) / k).den ∧
      ((m : ℚ) / k).den = k.toNat ∧ ((m : ℚ) / k).num = m := by
  obtain ⟨hk, hg, p, hp, hper⟩ := h
  obtain ⟨hden, hnum⟩ := den_num_div k m hk0 hg
  have hk0' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  refine ⟨p, hp, ?_, ?_, hden, hnum⟩
  · have := clear_den_thm k m hk0 hk p
    rw [hper] at this
    field_simp
    linarith
  · rw [hden]
    obtain ⟨t, ht⟩ := hk
    exact ⟨t.toNat, by omega⟩

/-- Rational periodic points: the denominator is `≡ ±1 (mod 6)`. -/
lemma den_pm1 (x : ℚ) (hx : Odd x.den) (p : ℕ) (hp : 0 < p) (hper : collatzQ^[p] x = x) :
    x.den % 6 = 1 ∨ x.den % 6 = 5 := by
  by_cases hx0 : x = 0
  · subst hx0; left; rfl
  obtain ⟨hne, -, hxv⟩ := periodic_eq_xv x hx p hp hper
  set v := parWord x p
  have hv1 : true ∈ v := by
    by_contra hv
    have hC : C v = 0 := by
      rw [C_eq_S3_pos]
      have : pos v = [] := List.eq_nil_of_length_eq_zero (by rw [pos_length]; exact List.count_eq_zero.mpr hv)
      rw [this]; rfl
    apply hx0
    rw [hxv]; simp [xv, hC]
  have hdvd : (x.den : ℤ) ∣ d v := by
    have hxv' : x = (C v : ℚ) / (d v : ℚ) := hxv
    have := den_div_dvd (C v) (d v)
    rw [show ((C v : ℤ) : ℚ) / ((d v : ℤ) : ℚ) = x by rw [hxv']; push_cast; rfl] at this
    exact this
  have hD6 := D6_thm v hv1
  have h3 : ¬ 3 ∣ x.den := by
    intro h
    have : (3 : ℤ) ∣ d v := (Int.natCast_dvd_natCast.mpr h).trans hdvd
    have h36 : (3 : ℕ) ∣ Int.gcd (d v) 6 := Int.dvd_gcd this (by norm_num)
    rw [hD6] at h36
    norm_num at h36
  obtain ⟨t, ht⟩ := hx
  omega

theorem bij3_thm : bij3 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨hx, hper⟩
    obtain ⟨p, hp, hper'⟩ := hper
    have hk0 : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
    show 0 < (x.den : ℤ) ∧ ((x.den : ℤ) % 6 = 1 ∨ (x.den : ℤ) % 6 = 5) ∧ InPrimCycle (x.den : ℤ) x.num
    refine ⟨hk0, ?_, ?_⟩
    · have := den_pm1 x hx p hp hper'
      omega
    · refine ⟨by exact_mod_cast hx, x.reduced, p, hp, ?_⟩
      have := clear_den_thm x.den x.num hk0 (by exact_mod_cast hx) p
      rw [show ((x.num : ℚ) / ((x.den : ℤ) : ℚ)) = x by push_cast; exact Rat.num_div_den x,
        hper'.eq] at this
      have e : ((x.den : ℤ) : ℚ) * x = x.num := by push_cast; exact Rat.mul_den_eq_num x |>.symm ▸ by ring
      rw [e] at this
      exact_mod_cast this.symm
  · intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    exact Rat.ext h.2 (by exact_mod_cast h.1)
  · rintro ⟨k, m⟩ ⟨hk0, _, hprim⟩
    obtain ⟨p, hp, hper, hodd, hden, hnum⟩ := prim_to_rat k m hk0 hprim
    refine ⟨(m : ℚ) / k, ⟨hodd, Function.mk_mem_periodicPts hp hper⟩, ?_⟩
    simp only [hden, hnum, Prod.mk.injEq, and_true]
    omega

/-! ## p. 44: no multiple of 3 in a cycle; the smallest member is `≡ ±1 (mod 6)` -/

theorem no3_thm : no3 := by
  intro k n hk h3 hn ⟨p, hp, hper⟩ h3n
  set c : ℕ → ℤ := fun j => (Tk k)^[j] n with hc
  have hstep : ∀ j, c (j + 1) = Tk k (c j) := fun j => Function.iterate_succ_apply' _ _ _
  -- going backwards: `3 ∣ c (j+1)` forces `c j` even and `3 ∣ c j`
  have back : ∀ j, (3 : ℤ) ∣ c (j + 1) → c j % 2 = 0 ∧ (3 : ℤ) ∣ c j := by
    intro j h
    have h2 := two_mul_Tk (n := c j) hk
    rw [← hstep] at h2
    split_ifs at h2 with hpar
    · refine ⟨hpar, ?_⟩
      rw [← h2]; exact dvd_mul_of_dvd_right h 2
    · exfalso
      have : (3 : ℤ) ∣ 3 * c j + k := by rw [← h2]; exact dvd_mul_of_dvd_right h 2
      exact h3 (by simpa using dvd_sub this (dvd_mul_right 3 (c j)))
  have hcp : c p = n := hper
  have hall : ∀ i, i ≤ p → (3 : ℤ) ∣ c (p - i) := by
    intro i
    induction i with
    | zero => intro _; simp [hcp, h3n]
    | succ i ih =>
      intro hi
      have := (back (p - (i + 1)) (by rw [show p - (i + 1) + 1 = p - i by omega]; exact ih (by omega))).2
      exact this
  have heven : ∀ j, j < p → c j % 2 = 0 := by
    intro j hj
    exact (back j (by have := hall (p - (j + 1)) (by omega); rwa [show p - (p - (j + 1)) = j + 1 by omega] at this)).1
  have hhalf : ∀ j, j ≤ p → 2 ^ j * c j = n := by
    intro j
    induction j with
    | zero => intro _; simp [hc]
    | succ j ih =>
      intro hj
      have h2 := two_mul_Tk (n := c j) hk
      rw [if_pos (heven j (by omega)), ← hstep] at h2
      rw [pow_succ, mul_assoc, h2, ih (by omega)]
  have := hhalf p le_rfl
  rw [hcp] at this
  have h2p : (2 : ℤ) ^ p ≠ 1 := by
    have : (1 : ℤ) < 2 ^ p := one_lt_pow₀ (by norm_num) hp.ne'
    omega
  apply hn
  have : (2 ^ p - 1) * n = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (by linarith : (2 : ℤ) ^ p = 1) h2p
  · exact h

theorem min_pm1_thm : min_pm1 := by
  intro k n hk h3 hn hcyc hmin
  have hodd : n % 2 = 1 := by
    by_contra h
    have h0 : n % 2 = 0 := by omega
    have := hmin 1
    simp only [Function.iterate_one, Tk_even h0] at this
    omega
  have := no3_thm k n hk h3 hn.ne' hcyc
  omega

/-! ## (3.8) and Theorem 3.5 -/

lemma C_ge (v : List Bool) : 3 ^ v.count true ≤ C v + 2 ^ v.count true := by
  induction v with
  | nil => simp [C]
  | cons b w ih =>
    cases b
    · simp only [C, Bool.false_eq_true, ↓reduceIte, zero_add, List.count_cons_of_ne (by decide : false ≠ true)]
      omega
    · simp only [C, ↓reduceIte, List.count_cons_self, pow_succ]
      omega

lemma C_le (v : List Bool) : C v + 2 ^ v.length ≤ 3 ^ v.length := by
  induction v with
  | nil => simp [C]
  | cons b w ih =>
    have h3 : 3 ^ w.count true ≤ 3 ^ w.length := Nat.pow_le_pow_right (by norm_num) (List.count_le_length)
    cases b
    · simp only [C, Bool.false_eq_true, ↓reduceIte, zero_add, List.length_cons, pow_succ]
      omega
    · simp only [C, ↓reduceIte, List.length_cons, pow_succ]
      omega

theorem eq3_8_thm : eq3_8 := by
  intro v hneg
  set n := v.length
  set l := v.count true
  have hln : l ≤ n := List.count_le_length
  have hdq : ((d v : ℤ) : ℚ) = (2 : ℚ) ^ n - 3 ^ l := d_cast v
  have hC0 : (0 : ℚ) ≤ (C v : ℚ) := by positivity
  have hd : (d v : ℚ) < 0 := by
    by_contra h
    push Not at h
    have : (0 : ℚ) ≤ xv v := div_nonneg hC0 h
    linarith
  have hge := C_ge v
  have hle := C_le v
  have h2 : (2 : ℕ) ^ l ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hln
  have hge' : (3 : ℚ) ^ l - 2 ^ n ≤ C v := by
    have : ((3 ^ l : ℕ) : ℚ) ≤ ((C v + 2 ^ l : ℕ) : ℚ) := by exact_mod_cast hge
    have h2' : ((2 ^ l : ℕ) : ℚ) ≤ ((2 ^ n : ℕ) : ℚ) := by exact_mod_cast h2
    push_cast at this h2'
    linarith
  have hxv : xv v = (C v : ℚ) / (d v : ℚ) := rfl
  refine ⟨?_, ?_⟩
  · rw [hxv, div_le_iff_of_neg hd]
    rw [hdq] at hd ⊢
    linarith
  · rw [hxv, div_eq_iff hd.ne, hdq]
    constructor
    · intro h
      have hCe : (C v : ℚ) = 3 ^ l - 2 ^ n := by linarith
      have h2n : (2 : ℚ) ^ n ≤ 2 ^ l := by
        have : ((3 ^ l : ℕ) : ℚ) ≤ ((C v + 2 ^ l : ℕ) : ℚ) := by exact_mod_cast hge
        push_cast at this
        linarith
      have h2n' : 2 ^ n ≤ 2 ^ l := by exact_mod_cast h2n
      have hnl : n ≤ l := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2n'
      have hcount : v.count true = v.length := le_antisymm hln hnl
      intro b hb
      have := List.count_eq_length.mp hcount
      exact (this b hb).symm
    · intro hall
      have hcount : l = n := List.count_eq_length.mpr fun b hb => (hall b hb).symm
      have hCe : (C v : ℚ) = 3 ^ n - 2 ^ n := by
        have h1 : ((3 ^ l : ℕ) : ℚ) ≤ ((C v + 2 ^ l : ℕ) : ℚ) := by exact_mod_cast hge
        have h2 : ((C v + 2 ^ n : ℕ) : ℚ) ≤ ((3 ^ n : ℕ) : ℚ) := by exact_mod_cast hle
        rw [hcount] at h1
        push_cast at h1 h2
        linarith
      rw [hCe, hcount]; ring

theorem thm3_5_thm : thm3_5 := by
  have part1 : ∀ n0 k : ℤ, n0 < 0 → |n0| < k → ¬ InPrimCycle k n0 := by
    intro n0 k hn0 hk hprim
    have hk0 : 0 < k := lt_of_le_of_lt (abs_nonneg n0) hk
    obtain ⟨p, hp, hper, hodd, -, -⟩ := prim_to_rat k n0 hk0 hprim
    obtain ⟨hne, -, hxv⟩ := periodic_eq_xv _ hodd p hp hper
    have hk0' : (0 : ℚ) < k := by exact_mod_cast hk0
    have hneg : (n0 : ℚ) / k < 0 := div_neg_of_neg_of_pos (by exact_mod_cast hn0) hk0'
    rw [hxv] at hneg
    have hle := (eq3_8_thm _ hneg).1
    rw [← hxv, div_le_iff₀ hk0'] at hle
    have : n0 ≤ -k := by exact_mod_cast (by linarith : (n0 : ℚ) ≤ -k)
    rw [abs_of_neg hn0] at hk
    omega
  refine ⟨part1, ⟨odd_one, by decide, 1, one_pos, by decide⟩, fun k hk => part1 (-1) k (by norm_num) (by simpa)⟩

/-! ## The examples of pp. 44–45 -/

lemma C_replicate_false (j : ℕ) : C (List.replicate j false) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, C, ih]

/-- If `x(v) = n0/k` (`k > 0` odd), then `n0` is `T_k`-periodic with period `|v|`. -/
lemma Tk_period_of_xv (v : List Bool) (hv : v ≠ []) (n0 k : ℤ) (hk0 : 0 < k) (hk : Odd k)
    (hx : xv v = (n0 : ℚ) / k) : (Tk k)^[v.length] n0 = n0 := by
  have hper := (thm2_1_thm v hv).2.1
  rw [hx] at hper
  have := clear_den_thm k n0 hk0 hk v.length
  rw [hper] at this
  have hk0' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  field_simp at this
  exact_mod_cast this.symm

theorem ex_10m_thm : ex_10m := by
  intro m hm
  have hv : xv (true :: List.replicate (m - 1) false) = 1 / (2 ^ m - 3) := by
    simp only [xv, LaboBP.d, C, ↓reduceIte, C_replicate_false, List.count_replicate, List.length_cons,
      List.length_replicate, List.count_cons_self]
    rw [show m - 1 + 1 = m by omega]
    simp
  refine ⟨hv, ?_⟩
  have h4 : (4 : ℤ) ≤ 2 ^ m := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hk0 : (0 : ℤ) < 2 ^ m - 3 := by omega
  have hk : Odd ((2 : ℤ) ^ m - 3) := by
    have : Even ((2 : ℤ) ^ m) := (even_two).pow_of_ne_zero (by omega)
    exact this.sub_odd (by decide)
  refine ⟨hk, by simp, m, by omega, ?_⟩
  have := Tk_period_of_xv _ (List.cons_ne_nil _ _) 1 _ hk0 hk (by rw [hv]; push_cast; ring)
  simpa [show m - 1 + 1 = m by omega] using this

lemma five_dvd_iff (m : ℕ) : (5 : ℤ) ∣ 2 ^ m - 9 ↔ m % 4 = 2 := by
  have hmod : (2 : ℤ) ^ m ≡ 2 ^ (m % 4) [ZMOD 5] := by
    conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul]
    have : (2 : ℤ) ^ 4 ≡ 1 [ZMOD 5] := by decide
    calc ((2 : ℤ) ^ 4) ^ (m / 4) * 2 ^ (m % 4) ≡ 1 ^ (m / 4) * 2 ^ (m % 4) [ZMOD 5] :=
          (this.pow _).mul_right _
      _ = 2 ^ (m % 4) := by simp
  have h2 : (2 : ℤ) ^ m - 9 ≡ 2 ^ (m % 4) - 9 [ZMOD 5] := hmod.sub_right 9
  have key : ∀ r, r < 4 → ((5 : ℤ) ∣ 2 ^ r - 9 ↔ r = 2) := by
    intro r hr
    interval_cases r <;> decide
  exact h2.dvd_iff.trans (key _ (Nat.mod_lt _ (by norm_num)))

theorem ex_5_thm : ex_5 := by
  intro m hm
  have hv : xv (true :: true :: List.replicate (m - 2) false) = 5 / (2 ^ m - 9) := by
    simp only [xv, LaboBP.d, C, ↓reduceIte, C_replicate_false, List.count_replicate, List.length_cons,
      List.length_replicate, List.count_cons_self]
    rw [show m - 2 + 1 + 1 = m by omega]
    norm_num
  refine ⟨hv, ?_⟩
  have h16 : (16 : ℤ) ≤ 2 ^ m := by
    calc (16 : ℤ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hk0 : (0 : ℤ) < 2 ^ m - 9 := by omega
  have hk : Odd ((2 : ℤ) ^ m - 9) := by
    have : Even ((2 : ℤ) ^ m) := (even_two).pow_of_ne_zero (by omega)
    exact this.sub_odd (by decide)
  have hgcd : Int.gcd 5 (2 ^ m - 9) = 1 ↔ m % 4 ≠ 2 := by
    rw [ne_eq, ← five_dvd_iff]
    have : Int.gcd 5 (2 ^ m - 9) = Nat.gcd 5 ((2 : ℤ) ^ m - 9).natAbs := rfl
    rw [this, ← Nat.Coprime, Nat.Prime.coprime_iff_not_dvd (by norm_num), Int.natCast_dvd.symm]
    rfl
  constructor
  · intro h; exact hgcd.mp h.2.1
  · intro h
    refine ⟨hk, hgcd.mpr h, m, by omega, ?_⟩
    have := Tk_period_of_xv _ (List.cons_ne_nil _ _) 5 _ hk0 hk (by rw [hv]; push_cast; ring)
    simpa [show m - 2 + 1 + 1 = m by omega] using this

/-! ## Theorem 3.4 -/

/-- The parities of the `T_k`-orbit of `n0` are the letters of `v`, when `x(v) = n0/k`. -/
lemma Tk_iter_parity (v : List Bool) (hv : v ≠ []) (n0 k : ℤ) (hk0 : 0 < k) (hk : Odd k)
    (hx : xv v = (n0 : ℚ) / k) (j : ℕ) (hj : j < v.length) :
    ((Tk k)^[j] n0 % 2 = 0 ↔ v[j] = false) := by
  have hpar := (parWord_eq_iff _ v).mp (thm2_1_thm v hv).2.2.1 j hj
  rw [hx] at hpar
  have hk0' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hc := clear_den_thm k n0 hk0 hk j
  have he : collatzQ^[j] ((n0 : ℚ) / k) = (((Tk k)^[j] n0 : ℤ) : ℚ) / k := by
    rw [← hc]; field_simp
  rw [he] at hpar
  have hnp := (num_parity ((Tk k)^[j] n0) k hk).1
  rw [← hpar]
  unfold par
  rcases Int.emod_two_eq_zero_or_one ((((Tk k)^[j] n0 : ℤ) : ℚ) / (k : ℚ)).num with h | h
  · simp [h, hnp.mp h]
  · have : ¬ (Tk k)^[j] n0 % 2 = 0 := fun h0 => by have := hnp.mpr h0; omega
    simp [h, this]

/-- The smallest-element argument of the proof of Theorem 3.4. -/
lemma n0_min (K n0 : ℤ) (n m : ℕ) (hK0 : 0 < K) (hK : Odd K) (hn0 : 0 < n0) (hn0odd : n0 % 2 = 1)
    (hbig : 2 ^ n * n0 < 3 * n0 + K) (hnm : 0 < n + m) (hper : (Tk K)^[n + m] n0 = n0)
    (heven : ∀ j, n ≤ j → j < n + m → (Tk K)^[j] n0 % 2 = 0) :
    ∀ j, n0 ≤ (Tk K)^[j] n0 := by
  set c : ℕ → ℤ := fun j => (Tk K)^[j] n0 with hc
  have hstep : ∀ j, c (j + 1) = Tk K (c j) := fun j => Function.iterate_succ_apply' _ _ _
  have h2 : ∀ j, 2 * c (j + 1) = if c j % 2 = 0 then c j else 3 * c j + K := fun j => by
    rw [hstep]; exact two_mul_Tk hK
  have hpos : ∀ j, 0 < c j := by
    intro j
    induction j with
    | zero => exact hn0
    | succ j ih => have := h2 j; split_ifs at this <;> omega
  have hhalf : ∀ j, c j ≤ 2 * c (j + 1) := fun j => by
    have := h2 j; have := hpos j; split_ifs at * <;> omega
  have h1 : 2 * c 1 = 3 * n0 + K := by have := h2 0; simp only [hc, Function.iterate_zero, id] at this; rw [if_neg (by omega)] at this; exact this
  have hlow : ∀ j, 1 ≤ j → 2 * c 1 ≤ 2 ^ j * c j := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj'
      · simp
      · have := ih hj'
        have := hhalf j
        calc 2 * c 1 ≤ 2 ^ j * c j := ih hj'
          _ ≤ 2 ^ j * (2 * c (j + 1)) := by gcongr
          _ = 2 ^ (j + 1) * c (j + 1) := by ring
  have hfirst : ∀ j, 1 ≤ j → j ≤ n → n0 < c j := by
    intro j hj hjn
    have hlo := hlow j hj
    have hpj : (2 : ℤ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hjn
    have hp0 : (0 : ℤ) < 2 ^ j := by positivity
    by_contra hcon
    push Not at hcon
    have : 2 ^ j * c j ≤ 2 ^ j * n0 := mul_le_mul_of_nonneg_left hcon hp0.le
    nlinarith
  have hlast : ∀ i, i ≤ m → c (n + m - i) = 2 ^ i * n0 := by
    intro i
    induction i with
    | zero => intro _; simp [hc, hper]
    | succ i ih =>
      intro hi
      have hj := heven (n + m - (i + 1)) (by omega) (by omega)
      have := h2 (n + m - (i + 1))
      rw [if_pos hj, show n + m - (i + 1) + 1 = n + m - i by omega, ih (by omega)] at this
      rw [← this]; ring
  intro j
  have hP : Function.IsPeriodicPt (Tk K) (n + m) n0 := hper
  rw [← hP.iterate_mod_apply j]
  set r := j % (n + m) with hr
  have hrlt : r < n + m := Nat.mod_lt _ hnm
  show n0 ≤ c r
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · rw [h0]; simp [hc]
  · by_cases hrn : r ≤ n
    · exact (hfirst r h0 hrn).le
    · have := hlast (n + m - r) (by omega)
      rw [show n + m - (n + m - r) = r by omega] at this
      rw [this]
      have : (1 : ℤ) ≤ 2 ^ (n + m - r) := one_le_pow₀ (by norm_num)
      nlinarith

lemma C_append_zeros (v : List Bool) (m : ℕ) : C (v ++ List.replicate m false) = C v := by
  rw [← phi_eq_C_thm, ← phi_eq_C_thm, phi_append_rep_false]

theorem thm3_4_thm : thm3_4 := by
  intro n0 hn0 ⟨k, hk0, hprim⟩
  obtain ⟨p, hp, hper, hodd, -, -⟩ := prim_to_rat k n0 hk0 hprim
  obtain ⟨hne, -, hxv⟩ := periodic_eq_xv _ hodd p hp hper
  obtain ⟨v, hv⟩ : ∃ v, v = parWord ((n0 : ℚ) / k) p := ⟨_, rfl⟩
  rw [← hv] at hne hxv
  obtain ⟨n, hn⟩ : ∃ n, n = v.length := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = v.count true := ⟨_, rfl⟩
  have hnpos : 0 < n := by rw [hn]; exact List.length_pos_iff.mpr hne
  have hk0' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hk : Odd k := hprim.1
  have hd0 : d v ≠ 0 := d_ne_zero v hne
  have hdodd : Odd (d v) := d_odd v hne
  have hdv : d v = 2 ^ n - 3 ^ l := by simp [LaboBP.d, hn, hl]
  have hxv' : (n0 : ℚ) / k = (C v : ℚ) / (d v : ℚ) := hxv
  have hd0' : ((d v : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hdpos : 0 < d v := by
    by_contra h
    push Not at h
    have h1 : (0 : ℚ) < (n0 : ℚ) / k := div_pos (by exact_mod_cast hn0) (by exact_mod_cast hk0)
    rw [hxv'] at h1
    have : (C v : ℚ) / (d v : ℚ) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by positivity) (by exact_mod_cast h)
    linarith
  have hcross : (C v : ℤ) * k = n0 * d v := by
    have h := hxv'
    rw [div_eq_div_iff hk0' hd0'] at h
    have : ((n0 * d v : ℤ) : ℚ) = ((C v * k : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this.symm
  obtain ⟨G, hG⟩ : k ∣ d v := by
    have hcop : IsCoprime k n0 := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hprim.2.1
    exact hcop.dvd_of_dvd_mul_left ⟨C v, by linarith [hcross]⟩
  have hNG : (C v : ℤ) = n0 * G := by
    have : (C v : ℤ) * k = n0 * G * k := by rw [hcross, hG]; ring
    exact mul_right_cancel₀ hk0.ne' this
  have hGpos : 0 < G := by
    by_contra h; push Not at h
    have : d v ≤ 0 := by rw [hG]; exact mul_nonpos_of_nonneg_of_nonpos hk0.le h
    omega
  have hGodd : Odd G := (Int.odd_mul.mp (hG ▸ hdodd)).2
  have hN0 : C v ≠ 0 := by
    intro h
    rw [h] at hNG
    have : 0 < n0 * G := mul_pos hn0 hGpos
    simp at hNG; omega
  obtain ⟨e, M, hModd, hNM⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  have hM0 : 0 < M := hModd.pos
  have hodd_dvd : ∀ a : ℤ, Odd a → a ∣ (C v : ℤ) → a ∣ (M : ℤ) := by
    intro a ha hdvd
    have h1 : a.natAbs ∣ 2 ^ e * M := by rw [← hNM]; exact Int.dvd_natCast.mp hdvd
    have h2 : a.natAbs ∣ M :=
      (Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr ha))).dvd_of_dvd_mul_left h1
    exact Int.dvd_natCast.mpr h2
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = M.totient := ⟨_, rfl⟩
  have hφpos : 0 < φ := by rw [hφ]; exact Nat.totient_pos.mpr hM0
  have hpow : ∀ c : ℕ, (M : ℤ) ∣ 2 ^ (c * φ) - 1 := by
    intro c
    have h1 : 2 ^ φ ≡ 1 [MOD M] := by rw [hφ]; exact Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hModd)
    have h2 : 2 ^ (c * φ) ≡ 1 [MOD M] := by
      rw [mul_comm, pow_mul]; simpa using h1.pow c
    have h3 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h2.symm
    have h4 : ((2 ^ (c * φ) - 1 : ℕ) : ℤ) = 2 ^ (c * φ) - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    rw [← h4]; exact_mod_cast h3
  have hGM : G ∣ (M : ℤ) := hodd_dvd G hGodd ⟨n0, by rw [hNG]; ring⟩
  -- the family `m_t = (t + 2n + 1)·φ`
  have hA : ∀ t : ℕ, ∃ A : ℤ, (2 : ℤ) ^ ((t + 2 * n + 1) * φ) - 1 = G * A :=
    fun t => hGM.trans (hpow _)
  choose A hA using hA
  have hApos : ∀ t, 0 ≤ A t := by
    intro t
    have h1 : (1 : ℤ) ≤ 2 ^ ((t + 2 * n + 1) * φ) := one_le_pow₀ (by norm_num)
    by_contra h; push Not at h
    have : G * A t < 0 := mul_neg_of_pos_of_neg hGpos h
    linarith [hA t]
  set km : ℕ → ℤ := fun t => k + 2 ^ n * A t with hkm
  have hkm0 : ∀ t, 0 < km t := fun t => by
    have := hApos t; have : (0 : ℤ) ≤ 2 ^ n * A t := by positivity
    simp only [hkm]; omega
  -- the word `w_t = v 0^{m_t}`
  have hdw : ∀ t, d (v ++ List.replicate ((t + 2 * n + 1) * φ) false) = G * km t := by
    intro t
    have hc0 : (List.replicate ((t + 2 * n + 1) * φ) false).count true = 0 :=
      List.count_eq_zero.mpr (by simp [List.mem_replicate])
    simp only [LaboBP.d, List.length_append, List.length_replicate, List.count_append, hc0,
      add_zero, ← hn, ← hl, hkm]
    have := hA t
    rw [hdv] at hG
    rw [pow_add]
    linear_combination hG + 2 ^ n * this
  have hkmodd : ∀ t, Odd (km t) := fun t => by
    have h := d_odd (v ++ List.replicate ((t + 2 * n + 1) * φ) false) (by simp [hne])
    rw [hdw t] at h
    exact (Int.odd_mul.mp h).2
  have hxw : ∀ t, xv (v ++ List.replicate ((t + 2 * n + 1) * φ) false) = (n0 : ℚ) / km t := by
    intro t
    have hG0 : (G : ℚ) ≠ 0 := by exact_mod_cast hGpos.ne'
    have hk0t : (km t : ℚ) ≠ 0 := by exact_mod_cast (hkm0 t).ne'
    rw [xv, C_append_zeros, hdw t]
    have : (C v : ℚ) = (n0 : ℚ) * G := by exact_mod_cast hNG
    rw [this]; push_cast; field_simp
  have hgcd : ∀ t, Int.gcd n0 (km t) = 1 := by
    intro t
    set g := Int.gcd n0 (km t)
    have hg1 : (g : ℤ) ∣ n0 := Int.gcd_dvd_left _ _
    have hg2 : (g : ℤ) ∣ km t := Int.gcd_dvd_right _ _
    have hgodd : Odd (g : ℤ) := by
      obtain ⟨c, hc⟩ := hg2
      have := hkmodd t
      rw [hc] at this
      exact (Int.odd_mul.mp this).1
    have hgG : (g : ℤ) * G ∣ (M : ℤ) :=
      hodd_dvd _ (Odd.mul hgodd hGodd) (by rw [hNG]; exact mul_dvd_mul_right hg1 G)
    have hgA : (g : ℤ) ∣ A t := by
      have : (g : ℤ) * G ∣ A t * G := by rw [mul_comm (A t), ← hA t]; exact hgG.trans (hpow _)
      exact Int.dvd_of_mul_dvd_mul_right hGpos.ne' this
    have hgk : (g : ℤ) ∣ k := by
      have : (g : ℤ) ∣ km t - 2 ^ n * A t := dvd_sub hg2 (dvd_mul_of_dvd_right hgA _)
      simpa [hkm] using this
    have : g ∣ Int.gcd n0 k := Int.dvd_gcd hg1 hgk
    rw [hprim.2.1] at this
    exact Nat.dvd_one.mp this
  have hprim_t : ∀ t, InPrimCycle (km t) n0 := by
    intro t
    refine ⟨hkmodd t, hgcd t, n + (t + 2 * n + 1) * φ, by omega, ?_⟩
    have := Tk_period_of_xv _ (by simp [hne]) n0 (km t) (hkm0 t) (hkmodd t) (hxw t)
    simpa [← hn] using this
  have hmono : StrictMono km := by
    apply strictMono_nat_of_lt_succ
    intro t
    have h1 : (2 : ℤ) ^ ((t + 2 * n + 1) * φ) < 2 ^ ((t + 1 + 2 * n + 1) * φ) :=
      pow_lt_pow_right₀ (by norm_num) (by nlinarith)
    have h2 : G * A t < G * A (t + 1) := by linarith [hA t, hA (t + 1)]
    have h3 : A t < A (t + 1) := lt_of_mul_lt_mul_left h2 hGpos.le
    have h4 : (2 : ℤ) ^ n * A t < 2 ^ n * A (t + 1) := by
      have : (0 : ℤ) < 2 ^ n := by positivity
      nlinarith
    simp only [hkm]; omega
  refine ⟨Set.infinite_of_injective_forall_mem hmono.injective fun t => ⟨hkm0 t, hprim_t t⟩, ?_⟩
  intro h6
  refine Set.infinite_of_injective_forall_mem hmono.injective fun t => ⟨hkm0 t, hprim_t t, ?_⟩
  -- `n0` is the smallest element
  have hn0odd : n0 % 2 = 1 := by omega
  have hAn0 : n0 ≤ A t := by
    have hCle := C_le v
    have h3n : (C v : ℤ) + 2 ^ n ≤ 3 ^ n := by rw [hn]; exact_mod_cast hCle
    have h34 : (3 : ℤ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have h4 : (4 : ℤ) ^ n * 2 ≤ 2 ^ ((t + 2 * n + 1) * φ) := by
      rw [show (4 : ℤ) ^ n * 2 = 2 ^ (2 * n + 1) by rw [pow_succ, pow_mul]; norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
    have h2n : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hGA : n0 * G ≤ G * A t := by rw [← hNG, ← hA t]; nlinarith
    by_contra h; push Not at h
    have : G * A t < G * n0 := mul_lt_mul_of_pos_left h hGpos
    nlinarith
  have hbig : 2 ^ n * n0 < 3 * n0 + km t := by
    have : (2 : ℤ) ^ n * n0 ≤ 2 ^ n * A t := mul_le_mul_of_nonneg_left hAn0 (by positivity)
    simp only [hkm]; omega
  have hlen : (v ++ List.replicate ((t + 2 * n + 1) * φ) false).length = n + (t + 2 * n + 1) * φ := by
    simp [hn]
  have hper' := Tk_period_of_xv _ (by simp [hne]) n0 (km t) (hkm0 t) (hkmodd t) (hxw t)
  rw [hlen] at hper'
  refine n0_min (km t) n0 n ((t + 2 * n + 1) * φ) (hkm0 t) (hkmodd t) hn0 hn0odd hbig
    (by omega) hper' ?_
  intro j hj1 hj2
  have hjl : j < (v ++ List.replicate ((t + 2 * n + 1) * φ) false).length := by rw [hlen]; exact hj2
  rw [Tk_iter_parity _ (by simp [hne]) n0 (km t) (hkm0 t) (hkmodd t) (hxw t) j hjl,
    List.getElem_append_right (by omega)]
  simp

end Lagarias
