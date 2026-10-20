import Mathlib
import Lagarias.L1990b_Enonces
import Lagarias.L3_Preuves

/-!
# Lagarias 1990 · Theorems 3.1 and 3.2 · proofs (phase 2b)

The proof of Theorem 3.1 is run over the PRIMES `p ≥ 5` of `(k0, A·k0]` (repairing the printed argument, which
runs over all integers `l` and may yield an even `l` or a multiple of 3, see the README). The analytic input is
either Chebyshev's bounds, which are in Mathlib (`thm3_1_65`, constant `6/5`), or the prime number theorem `H_PNT`
(`thm3_1`, the printed constant `5/4`). Theorem 3.2 then follows from `H_BF`.
-/

namespace Lagarias

open LaboBP LaboHH Chebyshev

/-! ## `k ∣ D(v)` and `S(t)` -/

theorem k_dvd_D_thm : k_dvd_D := by
  intro k n0 p hk0 hprim hp hper
  by_cases hk1 : k = 1
  · exact ⟨1, le_rfl, hp, by rw [hk1]; exact one_dvd _⟩
  have hk0' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  obtain ⟨hden, hnum⟩ := den_num_div k n0 hk0 hprim.2.1
  have hodd : Odd ((n0 : ℚ) / k).den := by
    rw [hden]; obtain ⟨t, ht⟩ := hprim.1; exact ⟨t.toNat, by omega⟩
  have hx : collatzQ^[p] ((n0 : ℚ) / k) = (n0 : ℚ) / k := by
    have := clear_den_thm k n0 hk0 hprim.1 p
    rw [hper] at this
    field_simp
    linarith
  obtain ⟨hne, hlen, hxv⟩ := periodic_eq_xv _ hodd p hp hx
  set v := parWord ((n0 : ℚ) / k) p
  have hdvd : (k : ℤ) ∣ d v := by
    have := den_div_dvd (C v) (d v)
    rw [show ((C v : ℤ) : ℚ) / ((d v : ℤ) : ℚ) = (n0 : ℚ) / k by rw [hxv]; push_cast; rfl, hden] at this
    rwa [Int.toNat_of_nonneg hk0.le] at this
  refine ⟨v.count true, ?_, ?_, ?_⟩
  · by_contra h0
    have hc0 : v.count true = 0 := by omega
    have hC : C v = 0 := by
      rw [C_eq_S3_pos]
      have : pos v = [] := List.eq_nil_of_length_eq_zero (by rw [pos_length]; exact hc0)
      rw [this]; rfl
    have hz : (n0 : ℚ) / k = 0 := by rw [hxv]; simp [xv, hC]
    have hn0 : n0 = 0 := by
      rcases div_eq_zero_iff.mp hz with h | h
      · exact_mod_cast h
      · exact absurd h hk0'
    have := hprim.2.1
    rw [hn0, Int.gcd_zero_left] at this
    omega
  · rw [← hlen]; exact List.count_le_length
  · simpa [LaboBP.d, hlen] using hdvd

lemma sum_sq_Icc (t : ℕ) : 6 * ∑ n ∈ Finset.Icc 1 t, n * n = t * (t + 1) * (2 * t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

theorem S31_bound_thm : S31_bound := by
  intro t
  have hfac : ∀ n ∈ Finset.Icc 1 t, ∀ l ∈ Finset.Icc 1 n,
      0 < ((2 : ℤ) ^ n - 3 ^ l).natAbs ∧ ((2 : ℤ) ^ n - 3 ^ l).natAbs ≤ 3 ^ n := by
    intro n hn l hl
    rw [Finset.mem_Icc] at hn hl
    refine ⟨Int.natAbs_pos.mpr ?_, ?_⟩
    · intro h
      have h2 : Even ((2 : ℤ) ^ n) := (even_two).pow_of_ne_zero (by omega)
      have h3 : Odd ((3 : ℤ) ^ l) := Odd.pow (by decide)
      rw [sub_eq_zero] at h
      rw [h] at h2
      exact (Int.not_even_iff_odd.mpr h3) h2
    · have h2 : (2 : ℤ) ^ n ≤ 3 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      have h3 : (3 : ℤ) ^ l ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hl.2
      have h2p : (0 : ℤ) < 2 ^ n := by positivity
      have h3p : (0 : ℤ) < 3 ^ l := by positivity
      have : |(2 : ℤ) ^ n - 3 ^ l| ≤ 3 ^ n := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have h4 : (((2 : ℤ) ^ n - 3 ^ l).natAbs : ℤ) ≤ ((3 ^ n : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]; push_cast; exact this
      exact_mod_cast h4
  refine ⟨Finset.prod_pos fun n hn => Finset.prod_pos fun l hl => (hfac n hn l hl).1, ?_⟩
  calc S31 t ≤ ∏ n ∈ Finset.Icc 1 t, (3 ^ n) ^ n := by
        unfold S31
        apply Finset.prod_le_prod' fun n hn => ?_
        have := Finset.prod_le_pow_card (Finset.Icc 1 n) _ (3 ^ n) fun l hl => (hfac n hn l hl).2
        simpa using this
    _ = 3 ^ (∑ n ∈ Finset.Icc 1 t, n * n) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        refine Finset.prod_congr rfl fun n _ => ?_
        rw [← pow_mul]
    _ = 3 ^ (t * (t + 1) * (2 * t + 1) / 6) := by
        rw [← sum_sq_Icc t]; congr 1; omega

/-! ## The core of Theorem 3.1 -/

/-- `T(t) = t(t+1)(2t+1)/6`. -/
def T31 (t : ℕ) : ℕ := t * (t + 1) * (2 * t + 1) / 6

lemma theta_sub_eq (k0 K : ℕ) (h : k0 ≤ K) :
    θ (K : ℝ) - θ (k0 : ℝ) = ∑ p ∈ (Finset.Ioc k0 K).filter Nat.Prime, Real.log p := by
  rw [theta_eq_sum_Icc, theta_eq_sum_Icc, Nat.floor_natCast, Nat.floor_natCast, sub_eq_iff_eq_add']
  rw [← Finset.sum_union]
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, hp⟩
      by_cases h3 : p ≤ k0
      · exact Or.inl ⟨⟨by omega, h3⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
    · rintro (⟨⟨_, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
      · exact ⟨⟨by omega, by omega⟩, hp⟩
      · exact ⟨⟨by omega, h2⟩, hp⟩
  · rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
    omega

lemma prime_mod6 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : (p : ℤ) % 6 = 1 ∨ (p : ℤ) % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
  omega

/-- If `θ(A·k0) − θ(k0) > log 3 · T(⌊c (A k0)^{1/3}⌋)` for all large `k0`, the set of Theorem 3.1 (with
constant `c`) is infinite. -/
theorem core31 (c : ℝ) (hc : 0 < c) (A : ℕ) (hA : 1 ≤ A)
    (hev : ∀ᶠ k0 : ℕ in Filter.atTop,
      Real.log 3 * (T31 ⌊c * ((A * k0 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) < θ ((A * k0 : ℕ) : ℝ) - θ (k0 : ℝ)) :
    {k : ℤ | 0 < k ∧ (k % 6 = 1 ∨ k % 6 = 5) ∧ NoShortPrimCycle k (c * (k : ℝ) ^ ((1 : ℝ) / 3))}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨k0, hk0, hk0B⟩ := (hev.and (Filter.eventually_ge_atTop (B.toNat + 5))).exists
  set K := A * k0 with hK
  set t := ⌊c * ((K : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ with ht
  have hk0K : k0 ≤ K := by rw [hK]; nlinarith
  set P := (Finset.Ioc k0 K).filter Nat.Prime with hP
  have hdvdS : ∀ p ∈ P, p ∣ S31 t := by
    intro p hpP
    simp only [hP, Finset.mem_filter, Finset.mem_Ioc] at hpP
    obtain ⟨⟨hp1, hp2⟩, hpr⟩ := hpP
    have hnot : (p : ℤ) ∉ {k : ℤ | 0 < k ∧ (k % 6 = 1 ∨ k % 6 = 5) ∧
        NoShortPrimCycle k (c * (k : ℝ) ^ ((1 : ℝ) / 3))} := by
      intro hmem
      have := hB hmem
      omega
    have hshort : ¬ NoShortPrimCycle p (c * ((p : ℤ) : ℝ) ^ ((1 : ℝ) / 3)) := fun hns =>
      hnot ⟨by exact_mod_cast hpr.pos, prime_mod6 p hpr (by omega), hns⟩
    simp only [NoShortPrimCycle, not_forall, not_lt] at hshort
    obtain ⟨n0, q, hprim, hq, hper, hqle⟩ := hshort
    obtain ⟨l, hl1, hlq, hdvd⟩ := k_dvd_D_thm p n0 q (by exact_mod_cast hpr.pos) hprim hq hper
    have hqt : q ≤ t := by
      apply Nat.le_floor
      refine hqle.trans ?_
      push_cast
      gcongr
    have h1 : p ∣ ((2 : ℤ) ^ q - 3 ^ l).natAbs := Int.natCast_dvd.mp hdvd
    have h2 : ((2 : ℤ) ^ q - 3 ^ l).natAbs ∣ ∏ l' ∈ Finset.Icc 1 q, ((2 : ℤ) ^ q - 3 ^ l').natAbs :=
      Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hl1, hlq⟩)
    have h3 : ∏ l' ∈ Finset.Icc 1 q, ((2 : ℤ) ^ q - 3 ^ l').natAbs ∣ S31 t :=
      Finset.dvd_prod_of_mem (fun n => ∏ l ∈ Finset.Icc 1 n, ((2 : ℤ) ^ n - 3 ^ l).natAbs)
        (Finset.mem_Icc.mpr ⟨hq, hqt⟩)
    exact h1.trans (h2.trans h3)
  have hprod : ∏ p ∈ P, p ∣ S31 t :=
    Finset.prod_primes_dvd _ (fun p hp => (Finset.mem_filter.mp hp).2.prime) hdvdS
  obtain ⟨hSpos, hSle⟩ := S31_bound_thm t
  have hle : ∏ p ∈ P, p ≤ 3 ^ T31 t := (Nat.le_of_dvd hSpos hprod).trans hSle
  have hlog : ∑ p ∈ P, Real.log p ≤ (T31 t : ℝ) * Real.log 3 := by
    have hpos : (0 : ℝ) < ∏ p ∈ P, (p : ℝ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
    rw [← Real.log_prod (fun p hp => by exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero),
      ← Real.log_pow]
    apply Real.log_le_log hpos
    have h := (Nat.cast_le (α := ℝ)).mpr hle
    push_cast at h
    exact h
  rw [theta_sub_eq k0 K hk0K] at hk0
  linarith

/-! ## Analytic lemmas -/

lemma T31_le (t : ℕ) (τ : ℝ) (ht : (t : ℝ) ≤ τ) (hτ : 100 ≤ τ) : (T31 t : ℝ) ≤ 0.33835 * τ ^ 3 := by
  have h1 : (T31 t : ℝ) ≤ ((t * (t + 1) * (2 * t + 1) : ℕ) : ℝ) / 6 := Nat.cast_div_le
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have h2 : ((t * (t + 1) * (2 * t + 1) : ℕ) : ℝ) ≤ τ * (τ + 1) * (2 * τ + 1) := by
    push_cast
    have : (t : ℝ) + 1 ≤ τ + 1 := by linarith
    have : 2 * (t : ℝ) + 1 ≤ 2 * τ + 1 := by linarith
    gcongr
  have h3 : τ * (τ + 1) * (2 * τ + 1) ≤ 2.0301 * τ ^ 3 := by
    have hs : 0 ≤ τ - 100 := by linarith
    have key : 0 ≤ τ * (3.02 * (τ - 100) + 0.0301 * (τ - 100) ^ 2) := by positivity
    nlinarith [key]
  linarith

lemma cube_rpow (y : ℝ) (hy : 0 ≤ y) : (y ^ ((1 : ℝ) / 3)) ^ 3 = y := by
  rw [one_div, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
  exact Real.rpow_inv_natCast_pow hy (by norm_num)

lemma le_cube_rpow (a y : ℝ) (ha : 0 ≤ a) (h : a ^ 3 ≤ y) : a ≤ y ^ ((1 : ℝ) / 3) := by
  have e : (a ^ 3) ^ ((1 : ℝ) / 3) = a := by
    rw [one_div, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
    exact Real.pow_rpow_inv_natCast ha (by norm_num)
  rw [← e]
  exact Real.rpow_le_rpow (by positivity) h (by norm_num)

lemma log_three_le : Real.log 3 ≤ 1.10223 := by
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h98 : Real.log 9 = Real.log 8 + Real.log (9 / 8) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hl : Real.log (9 / 8) ≤ 9 / 8 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 := Real.log_two_lt_d9
  linarith

lemma sqrt_mul_log_isLittleO : (fun u : ℝ => √u * Real.log u) =o[Filter.atTop] id := by
  have h := (Asymptotics.isBigO_refl (fun u : ℝ => √u) Filter.atTop).mul_isLittleO
    (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num))
  refine h.congr' Filter.EventuallyEq.rfl ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with u hu
  rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hu]
  rfl

lemma err100 : ∀ᶠ x : ℝ in Filter.atTop,
    Real.log (100 * x + 1) + 2 * √(100 * x) * Real.log (100 * x) ≤ x := by
  have hT : Filter.Tendsto (fun x : ℝ => 100 * x) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num)
  have hT1 : Filter.Tendsto (fun x : ℝ => 100 * x + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 hT
  have hO1 : (fun x : ℝ => 100 * x + 1) =O[Filter.atTop] (id : ℝ → ℝ) := by
    refine Asymptotics.IsBigO.of_bound 101 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    simp only [id, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  have hO2 : (fun x : ℝ => 100 * x) =O[Filter.atTop] (id : ℝ → ℝ) :=
    Asymptotics.isBigO_const_mul_self 100 id Filter.atTop
  have h1 : (fun x : ℝ => Real.log (100 * x + 1)) =o[Filter.atTop] (id : ℝ → ℝ) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hT1).trans_isBigO hO1
  have h2 : (fun x : ℝ => √(100 * x) * Real.log (100 * x)) =o[Filter.atTop] (id : ℝ → ℝ) :=
    (sqrt_mul_log_isLittleO.comp_tendsto hT).trans_isBigO hO2
  have h := (h1.add (h2.const_mul_left 2)).def (c := 1) (by norm_num)
  filter_upwards [h, Filter.eventually_ge_atTop 0] with x hx hx0
  simp only [id, Real.norm_eq_abs, one_mul, abs_of_nonneg hx0] at hx
  have := le_abs_self (Real.log (100 * x + 1) + 2 * (√(100 * x) * Real.log (100 * x)))
  linarith [mul_assoc (2 : ℝ) (√(100 * x)) (Real.log (100 * x))]

/-! ## Theorem 3.1 -/

/-- Theorem 3.1 with the constant `6/5`: no hypothesis (Chebyshev's bounds of Mathlib). -/
theorem thm3_1_65_thm : thm3_1_65 := by
  have := core31 (6 / 5) (by norm_num) 100 (by norm_num) ?_
  · exact this
  have hev := (tendsto_natCast_atTop_atTop.eventually err100).and (Filter.eventually_ge_atTop 6000)
  filter_upwards [hev] with k0 ⟨herr, hk0⟩
  set x : ℝ := (k0 : ℝ) with hx
  have hx0 : (6000 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hk0
  have hK : ((100 * k0 : ℕ) : ℝ) = 100 * x := by push_cast; ring
  -- upper bound for the left side
  set τ := 6 / 5 * (100 * x) ^ ((1 : ℝ) / 3) with hτ
  have h84 : (84 : ℝ) ≤ (100 * x) ^ ((1 : ℝ) / 3) := le_cube_rpow 84 _ (by norm_num) (by nlinarith)
  have hτ100 : 100 ≤ τ := by rw [hτ]; linarith
  have ht : ((⌊6 / 5 * ((100 * k0 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) ≤ τ := by
    rw [hK]; exact Nat.floor_le (by positivity)
  have hT := T31_le _ τ ht hτ100
  have hτ3 : τ ^ 3 = 172.8 * x := by
    rw [hτ, mul_pow, cube_rpow _ (by positivity)]; ring
  have hl3 := log_three_le
  have hl3p : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlhs : Real.log 3 * (T31 ⌊6 / 5 * ((100 * k0 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) ≤ 64.45 * x := by
    calc Real.log 3 * (T31 ⌊6 / 5 * ((100 * k0 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ)
        ≤ 1.10223 * (0.33835 * τ ^ 3) := mul_le_mul hl3 hT (by positivity) (by norm_num)
      _ ≤ 64.45 * x := by rw [hτ3]; nlinarith
  -- lower bound for the right side
  have hge := theta_ge (100 * k0)
  have hle := theta_le_log4_mul_x (x := x) (by positivity)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_gt_d9
  rw [hK] at hge
  have h2x : 0.6931471803 * x ≤ Real.log 2 * x := by nlinarith
  have : θ ((100 * k0 : ℕ) : ℝ) - θ x ≥ 66.9 * x := by
    rw [hK]
    have e1 : 100 * x * Real.log 2 = 100 * (Real.log 2 * x) := by ring
    have e2 : Real.log 4 * x = 2 * (Real.log 2 * x) := by rw [hl4]; ring
    linarith
  linarith

/-- Theorem 3.1 with the printed constant `5/4`, under the prime number theorem. -/
theorem thm3_1_thm : thm3_1 := by
  intro hPNT
  have := core31 (5 / 4) (by norm_num) 5 (by norm_num) ?_
  · exact this
  have hθ : ∀ᶠ y : ℝ in Filter.atTop, 0.98 * y ≤ θ y ∧ θ y ≤ 1.02 * y := by
    have h := hPNT.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 0.02))
    filter_upwards [h, Filter.eventually_gt_atTop 0] with y hy hy0
    rw [Real.dist_eq, abs_lt] at hy
    obtain ⟨h1, h2⟩ := hy
    have e1 : 0.98 < θ y / y := by linarith
    have e2 : θ y / y < 1.02 := by linarith
    rw [lt_div_iff₀ hy0] at e1
    rw [div_lt_iff₀ hy0] at e2
    exact ⟨e1.le, e2.le⟩
  have hθ5 : ∀ᶠ y : ℝ in Filter.atTop, 0.98 * (5 * y) ≤ θ (5 * y) :=
    (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 5)).eventually (hθ.mono fun y h => h.1)
  have hev := (tendsto_natCast_atTop_atTop.eventually (hθ.and hθ5)).and
    (Filter.eventually_ge_atTop 102400)
  filter_upwards [hev] with k0 ⟨⟨⟨_, hθ1⟩, hθ2⟩, hk0⟩
  set x : ℝ := (k0 : ℝ) with hx
  have hx0 : (102400 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hk0
  have hK : ((5 * k0 : ℕ) : ℝ) = 5 * x := by push_cast; ring
  set τ := 5 / 4 * (5 * x) ^ ((1 : ℝ) / 3) with hτ
  have h80 : (80 : ℝ) ≤ (5 * x) ^ ((1 : ℝ) / 3) := le_cube_rpow 80 _ (by norm_num) (by nlinarith)
  have hτ100 : 100 ≤ τ := by rw [hτ]; linarith
  have ht : ((⌊5 / 4 * ((5 * k0 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) ≤ τ := by
    rw [hK]; exact Nat.floor_le (by positivity)
  have hT := T31_le _ τ ht hτ100
  have hτ3 : τ ^ 3 = 9.765625 * x := by
    rw [hτ, mul_pow, cube_rpow _ (by positivity)]; ring
  have hl3 := log_three_le
  have hlhs : Real.log 3 * (T31 ⌊5 / 4 * ((5 * k0 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) ≤ 3.65 * x := by
    calc Real.log 3 * (T31 ⌊5 / 4 * ((5 * k0 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ)
        ≤ 1.10223 * (0.33835 * τ ^ 3) := mul_le_mul hl3 hT (by positivity) (by norm_num)
      _ ≤ 3.65 * x := by rw [hτ3]; nlinarith
  rw [hK] at hlhs ⊢
  linarith

/-! ## Theorem 3.2 -/

lemma logb_threshold (c : ℝ) : ∃ P0 : ℝ, ∀ x : ℝ, P0 ≤ x → 1 + c * Real.logb 2 x ≤ x / 6 := by
  have h1 : (fun _ : ℝ => (1 : ℝ)) =o[Filter.atTop] (id : ℝ → ℝ) :=
    Asymptotics.isLittleO_const_id_atTop 1
  have h2 : (fun x : ℝ => c * Real.logb 2 x) =o[Filter.atTop] (id : ℝ → ℝ) := by
    have : (fun x : ℝ => c * Real.logb 2 x) = fun x => (c / Real.log 2) * Real.log x := by
      funext x; rw [Real.logb]; ring
    rw [this]
    exact Real.isLittleO_log_id_atTop.const_mul_left _
  have h := (h1.add h2).def (c := 1 / 6) (by norm_num)
  obtain ⟨P0, hP0⟩ := Filter.eventually_atTop.mp (h.and (Filter.eventually_ge_atTop 0))
  refine ⟨P0, fun x hx => ?_⟩
  obtain ⟨hb, hx0⟩ := hP0 x hx
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hx0] at hb
  have := le_abs_self (1 + c * Real.logb 2 x)
  linarith

theorem thm3_2_thm : thm3_2 := by
  rintro ⟨c1, hBF⟩
  obtain ⟨P0, hP0⟩ := logb_threshold |c1|
  set Q := max P0 2 with hQ
  have hQ2 : (2 : ℝ) ≤ Q := le_max_right _ _
  set K1 : ℕ := ⌈(Q / (6 / 5)) ^ 3⌉₊ with hK1
  refine ((thm3_1_65_thm.diff (Set.finite_Ioo (0 : ℤ) K1)).mono ?_)
  rintro k ⟨⟨hk0, hk6, hns⟩, hkK⟩
  have hkK1 : (K1 : ℤ) ≤ k := by
    simp only [Set.mem_Ioo, not_and, not_lt] at hkK
    exact hkK hk0
  refine ⟨hk0, hk6, ?_⟩
  intro n0 p hprim hp hper
  have hpgt := hns n0 p hprim hp hper
  have hkR : (Q / (6 / 5)) ^ 3 ≤ (k : ℝ) := by
    have h1 : (Q / (6 / 5)) ^ 3 ≤ (K1 : ℝ) := Nat.le_ceil _
    have h2 : ((K1 : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkK1
    push_cast at h2
    linarith
  have hk13 : Q / (6 / 5) ≤ (k : ℝ) ^ ((1 : ℝ) / 3) := le_cube_rpow _ _ (by positivity) hkR
  have hpQ : Q < (p : ℝ) := by
    have : Q = 6 / 5 * (Q / (6 / 5)) := by ring
    linarith [mul_le_mul_of_nonneg_left hk13 (by norm_num : (0 : ℝ) ≤ 6 / 5)]
  have hp2 : 2 ≤ p := by
    have : (2 : ℝ) < p := lt_of_le_of_lt hQ2 hpQ
    exact_mod_cast this.le
  set v := parWord ((n0 : ℚ) / k) p with hv
  have hvl : v.length = p := parWord_length _ _
  have hD := hBF p (v.count true) hp2
  have hdv : ((d v : ℤ) : ℝ) = (2 : ℝ) ^ p - 3 ^ v.count true := by
    rw [show ((d v : ℤ) : ℝ) = (((d v : ℤ) : ℚ) : ℝ) by push_cast; rfl, d_cast, hvl]; push_cast; rfl
  have hpR : (0 : ℝ) < p := by positivity
  have hA : (0 : ℝ) < 1 / 2 * (p : ℝ) ^ (-c1) * 2 ^ p := by positivity
  have hlog : Real.logb 2 (1 / 2 * (p : ℝ) ^ (-c1) * 2 ^ p) = p - 1 - c1 * Real.logb 2 p := by
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
      Real.logb_rpow_eq_mul_logb_of_pos hpR, Real.logb_pow, Real.logb_self_eq_one (by norm_num),
      one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    ring
  have hmono : p - 1 - c1 * Real.logb 2 p ≤ Real.logb 2 |((d v : ℤ) : ℝ)| := by
    rw [← hlog, hdv]
    exact Real.logb_le_logb_of_le (by norm_num) hA hD
  have hthr := hP0 p (le_trans (le_max_left _ _) hpQ.le)
  have hlogp : 0 ≤ Real.logb 2 p := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ p))
  have hc1 : c1 * Real.logb 2 p ≤ |c1| * Real.logb 2 p := mul_le_mul_of_nonneg_right (le_abs_self c1) hlogp
  have hk3 : (k : ℝ) ^ ((1 : ℝ) / 3) ≤ Real.logb 2 |((d v : ℤ) : ℝ)| := by
    have : (k : ℝ) ^ ((1 : ℝ) / 3) < 5 / 6 * p := by linarith
    linarith
  have hk0' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0.le
  calc (k : ℝ) = ((k : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := (cube_rpow _ hk0').symm
    _ ≤ (Real.logb 2 |((d v : ℤ) : ℝ)|) ^ 3 := pow_le_pow_left₀ (by positivity) hk3 3

end Lagarias
