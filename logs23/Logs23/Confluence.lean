import Mathlib
import Logs23.ExpKernel

/-!
# Logs23 · from the exponential kernel to the confluent determinant `D(x) = det [(xζ_j)^κ e^{λ_l x ζ_j}]`

Rows `i : Fin (L * (K + 1))` correspond to pairs `(l, κ) ∈ Fin L × Fin (K + 1)` by `finProdFinEquiv`
(`i = κ + (K + 1) l`, lexicographic order, `l` major); `λ_l = (l + 1) log 2`; `μ_h i = λ_l + κ h`.
* `det [e^{μ_h i x ζ_j}] = h^σ · det [e^{λ_l x ζ_j} w_j^κ]`, `w_j = (e^{h x ζ_j} − 1)/h`, `σ = Σ_i κ`
  (a lower triangular change of rows);
* as `h → 0+`, the right-hand determinant tends to `D(x)`;
* `vprod μ_h ≥ h^σ ((log 2)/2)^(tri N)` for small `h`;
hence, from `Logs23/ExpKernel.lean`, `|D(1)| ≥ (∏ 1/m!) ((log 2)/2)^(tri N) |V(ζ)|` and `|D(1)| ≤ x^(−tri N) |D(x)|`.
-/

namespace Logs23

open Matrix Finset Filter Topology

open scoped Nat

noncomputable section

variable {L K : ℕ}

/-- The pair `(l, κ)` of a row. -/
abbrev pr (i : Fin (L * (K + 1))) : Fin L × Fin (K + 1) := finProdFinEquiv.symm i

theorem val_eq_pr (i : Fin (L * (K + 1))) : (i : ℕ) = ((pr i).2 : ℕ) + (K + 1) * ((pr i).1 : ℕ) := by
  conv_lhs => rw [← finProdFinEquiv.apply_symm_apply i]
  rfl

/-- `λ_l = (l + 1) log 2`. -/
def lam (l : Fin L) : ℝ := ((l : ℕ) + 1 : ℝ) * Real.log 2

/-- `μ_h i = λ_l + κ h`. -/
def muh (h : ℝ) (i : Fin (L * (K + 1))) : ℝ := lam (pr i).1 + ((pr i).2 : ℕ) * h

/-- `σ = Σ_i κ`. -/
def sig (L K : ℕ) : ℕ := ∑ i : Fin (L * (K + 1)), ((pr i).2 : ℕ)

/-- The confluent determinant `D(x) = det [(x ζ_j)^κ e^{λ_l x ζ_j}]`. -/
def Dc (ζ : Fin (L * (K + 1)) → ℝ) (x : ℝ) : ℝ :=
  (Matrix.of fun i j => (x * ζ j) ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * (x * ζ j))).det

/-- `w_h(z) = (e^{h z} − 1)/h`. -/
def wh (h z : ℝ) : ℝ := (Real.exp (h * z) - 1) / h

/-- The determinant after the triangular change of rows. -/
def Wd (ζ : Fin (L * (K + 1)) → ℝ) (h x : ℝ) : ℝ :=
  (Matrix.of fun i j => Real.exp (lam (pr i).1 * (x * ζ j)) * wh h (x * ζ j) ^ ((pr i).2 : ℕ)).det

/-! ## Order of the rows -/

/-- For `i < j`: either the block of `i` is earlier, or it is the same block with a smaller `κ`. -/
theorem lt_cases {i j : Fin (L * (K + 1))} (hij : i < j) :
    (pr i).1 < (pr j).1 ∨ ((pr i).1 = (pr j).1 ∧ (pr i).2 < (pr j).2) := by
  have hi := val_eq_pr i
  have hj := val_eq_pr j
  have hlt : (i : ℕ) < j := hij
  have hki := (pr i).2.2
  have hkj := (pr j).2.2
  rcases lt_trichotomy ((pr i).1 : ℕ) ((pr j).1 : ℕ) with h | h | h
  · exact Or.inl (Fin.lt_def.mpr h)
  · right
    refine ⟨Fin.ext h, Fin.lt_def.mpr ?_⟩
    rw [h] at hi
    omega
  · exfalso
    have : (K + 1) * ((pr j).1 : ℕ) + (K + 1) ≤ (K + 1) * ((pr i).1 : ℕ) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega

/-! ## The triangular factorization -/

/-- The change of rows: `U[(l,κ),(l',ι)] = [l = l'] [ι ≤ κ] C(κ, ι) h^ι`. -/
def Um (h : ℝ) : Matrix (Fin (L * (K + 1))) (Fin (L * (K + 1))) ℝ := fun i i' =>
  if (pr i').1 = (pr i).1 ∧ (pr i').2 ≤ (pr i).2 then
    (((pr i).2 : ℕ).choose ((pr i').2 : ℕ) : ℝ) * h ^ ((pr i').2 : ℕ) else 0

theorem Um_lowerTriangular (h : ℝ) : (Um (L := L) (K := K) h).IsLowerTriangular := by
  intro i i' hii'
  have h' : i < i' := hii'
  simp only [Um]
  rw [if_neg]
  rintro ⟨hl, hk⟩
  rcases lt_cases h' with h1 | ⟨_, h2⟩
  · exact (lt_irrefl _) (hl ▸ h1)
  · exact (not_lt.mpr hk) h2

theorem det_Um (h : ℝ) : (Um (L := L) (K := K) h).det = h ^ sig L K := by
  rw [Matrix.det_of_isLowerTriangular _ (Um_lowerTriangular h), sig, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Um]

/-- The row sum giving the exponential back. -/
theorem sum_row (h z : ℝ) (hh : h ≠ 0) (i : Fin (L * (K + 1))) :
    ∑ i', Um h i i' * (Real.exp (lam (pr i').1 * z) * wh h z ^ ((pr i').2 : ℕ)) =
      Real.exp (muh h i * z) := by
  set q := (pr i).2 with hq
  set E := Real.exp (lam (pr i).1 * z) with hE
  -- pass to pairs; only the block of `i` contributes
  have h1 : ∑ i', Um h i i' * (Real.exp (lam (pr i').1 * z) * wh h z ^ ((pr i').2 : ℕ)) =
      ∑ ι : Fin (K + 1), (if ι ≤ q then ((q : ℕ).choose (ι : ℕ) : ℝ) * h ^ (ι : ℕ) else 0) *
        (E * wh h z ^ (ι : ℕ)) := by
    rw [← (finProdFinEquiv).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single (pr i).1]
    · refine Finset.sum_congr rfl fun ι _ => ?_
      simp only [Um, pr, Equiv.symm_apply_apply, true_and, hq, hE]
    · intro l _ hl
      refine Finset.sum_eq_zero fun ι _ => ?_
      simp only [Um, pr, Equiv.symm_apply_apply]
      rw [if_neg (fun h' => hl h'.1), zero_mul]
    · simp
  have hqK : (q : ℕ) < K + 1 := q.2
  have h2 : ∑ ι : Fin (K + 1), (if ι ≤ q then ((q : ℕ).choose (ι : ℕ) : ℝ) * h ^ (ι : ℕ) else 0) *
        (E * wh h z ^ (ι : ℕ)) =
      ∑ m ∈ Finset.range (K + 1), (if m ≤ (q : ℕ) then ((q : ℕ).choose m : ℝ) * h ^ m else 0) *
        (E * wh h z ^ m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (if m ≤ (q : ℕ) then ((q : ℕ).choose m : ℝ) * h ^ m else 0) *
        (E * wh h z ^ m)) (K + 1)]
    refine Finset.sum_congr rfl fun ι _ => ?_
    simp only [Fin.le_def]
  have h3 : ∑ m ∈ Finset.range (K + 1), (if m ≤ (q : ℕ) then ((q : ℕ).choose m : ℝ) * h ^ m else 0) *
        (E * wh h z ^ m) =
      E * ∑ m ∈ Finset.range ((q : ℕ) + 1), (h * wh h z) ^ m * 1 ^ ((q : ℕ) - m) * ((q : ℕ).choose m : ℝ) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show (q : ℕ) + 1 ≤ K + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico ((q : ℕ) + 1) (K + 1)) (fun m hm => by
      rw [Finset.mem_Ico] at hm; rw [if_neg (by omega), zero_mul]), add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [if_pos (by omega), one_pow, mul_one, mul_pow]
    ring
  rw [h1, h2, h3, ← add_pow]
  have hw : h * wh h z + 1 = Real.exp (h * z) := by
    simp only [wh]; field_simp; ring
  rw [hw, ← Real.exp_nat_mul, hE, ← Real.exp_add, muh]
  congr 1
  rw [hq]
  ring

theorem conf_factor (ζ : Fin (L * (K + 1)) → ℝ) {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    (Ek (muh h) ζ x).det = h ^ sig L K * Wd ζ h x := by
  have hmat : Ek (muh h) ζ x = Um h * Matrix.of fun i j =>
      Real.exp (lam (pr i).1 * (x * ζ j)) * wh h (x * ζ j) ^ ((pr i).2 : ℕ) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Ek]
    exact (sum_row h (x * ζ j) hh i).symm
  rw [hmat, Matrix.det_mul, det_Um, Wd]

/-! ## The limit `h → 0` -/

theorem tendsto_wh (z : ℝ) : Tendsto (fun h => wh h z) (𝓝[≠] 0) (𝓝 z) := by
  have hd : HasDerivAt (fun t => Real.exp (t * z)) z 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const z).exp
    simpa using this
  have := hd.tendsto_slope_zero
  refine this.congr' (Eventually.of_forall fun t => ?_)
  simp [wh, smul_eq_mul, div_eq_inv_mul]

theorem tendsto_Wd (ζ : Fin (L * (K + 1)) → ℝ) (x : ℝ) :
    Tendsto (fun h => Wd ζ h x) (𝓝[≠] 0) (𝓝 (Dc ζ x)) := by
  have hmat : Tendsto (fun h => (Matrix.of fun i j =>
      Real.exp (lam (pr i).1 * (x * ζ j)) * wh h (x * ζ j) ^ ((pr i).2 : ℕ) :
        Matrix (Fin (L * (K + 1))) (Fin (L * (K + 1))) ℝ)) (𝓝[≠] 0)
      (𝓝 (Matrix.of fun i j => (x * ζ j) ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * (x * ζ j)))) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    simp only [Matrix.of_apply]
    rw [mul_comm ((x * ζ j) ^ _)]
    exact tendsto_const_nhds.mul ((tendsto_wh (x * ζ j)).pow _)
  exact ((continuous_id.matrix_det).tendsto _).comp hmat

/-! ## The nodes `μ_h` -/

theorem muh_sub_of_lt {h : ℝ} (hh : 0 ≤ h) {i j : Fin (L * (K + 1))} (hij : i < j) :
    ((pr i).1 = (pr j).1 → h ≤ muh h j - muh h i) ∧
      ((pr i).1 ≠ (pr j).1 → Real.log 2 - K * h ≤ muh h j - muh h i) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkj : ((pr j).2 : ℕ) ≤ K := Nat.lt_succ_iff.mp (pr j).2.2
  have hki : ((pr i).2 : ℕ) ≤ K := Nat.lt_succ_iff.mp (pr i).2.2
  rcases lt_cases hij with h1 | ⟨h1, h2⟩
  · refine ⟨fun h' => absurd h' (ne_of_lt h1), fun _ => ?_⟩
    have hl : ((pr i).1 : ℕ) + 1 ≤ (pr j).1 := h1
    have hlr : ((pr i).1 : ℝ) + 1 ≤ (pr j).1 := by exact_mod_cast hl
    have hkr : (((pr j).2 : ℕ) : ℝ) ≥ 0 := by positivity
    have hkir : (((pr i).2 : ℕ) : ℝ) ≤ K := by exact_mod_cast hki
    simp only [muh, lam]
    nlinarith
  · refine ⟨fun _ => ?_, fun h' => absurd h1 h'⟩
    have hk : ((pr i).2 : ℕ) + 1 ≤ (pr j).2 := h2
    have hkr : (((pr i).2 : ℕ) : ℝ) + 1 ≤ ((pr j).2 : ℕ) := by exact_mod_cast hk
    simp only [muh, lam, h1]
    nlinarith

theorem muh_strictMono {h : ℝ} (hh : 0 < h) (hK : K * h < Real.log 2) :
    StrictMono (muh (L := L) (K := K) h) := by
  intro i j hij
  obtain ⟨h1, h2⟩ := muh_sub_of_lt hh.le hij
  by_cases hb : (pr i).1 = (pr j).1
  · linarith [h1 hb]
  · linarith [h2 hb]

theorem muh_pos {h : ℝ} (hh : 0 ≤ h) (i : Fin (L * (K + 1))) : 0 < muh (L := L) (K := K) h i := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [muh, lam]
  positivity

/-- `#{i < j in the block of j} ≤ κ_j`. -/
theorem card_same_le (j : Fin (L * (K + 1))) :
    ((Finset.Iio j).filter (fun i => (pr i).1 = (pr j).1)).card ≤ ((pr j).2 : ℕ) := by
  have : ((Finset.Iio j).filter (fun i => (pr i).1 = (pr j).1)).card ≤
      (Finset.Iio (pr j).2).card := by
    refine Finset.card_le_card_of_injOn (fun i => (pr i).2) (fun i hi => ?_) (fun a ha b hb hab => ?_)
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Iio] at hi
      rcases lt_cases hi.1 with h1 | ⟨_, h2⟩
      · exact absurd hi.2 (ne_of_lt h1)
      · simpa using h2
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Iio] at ha hb
      have hpa : pr a = pr b := Prod.ext (ha.2.trans hb.2.symm) hab
      exact finProdFinEquiv.symm.injective hpa
  simpa using this

theorem prod_Iio_eq_prod_Ioi {N : ℕ} (f : Fin N → Fin N → ℝ) :
    ∏ i : Fin N, ∏ j ∈ Ioi i, f i j = ∏ j : Fin N, ∏ i ∈ Iio j, f i j := by
  rw [show (∏ i : Fin N, ∏ j ∈ Ioi i, f i j) = ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 from
    Finset.prod_congr rfl fun i _ => by rw [← Finset.prod_filter]; congr 1; ext j; simp]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_filter]; congr 1; ext i; simp

/-- `vprod μ_h ≥ h^σ ((log 2)/2)^(tri N)` for `0 < h ≤ 1` and `K h ≤ (log 2)/2`. -/
theorem vprod_muh_ge {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (hK : K * h ≤ Real.log 2 / 2) :
    h ^ sig L K * (Real.log 2 / 2) ^ tri (L * (K + 1)) ≤ vprod (muh (L := L) (K := K) h) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  set c := Real.log 2 / 2 with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by linarith
  rw [vprod, prod_Iio_eq_prod_Ioi, sig, tri, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
  -- one column `j`
  set A := (Finset.Iio j).filter (fun i => (pr i).1 = (pr j).1) with hA
  set B := (Finset.Iio j).filter (fun i => ¬ (pr i).1 = (pr j).1) with hB
  have hfac : ∀ i ∈ Finset.Iio j,
      (if (pr i).1 = (pr j).1 then h else c) ≤ muh h j - muh h i := by
    intro i hi
    obtain ⟨hs, hx⟩ := muh_sub_of_lt hh.le (Finset.mem_Iio.mp hi)
    by_cases hb : (pr i).1 = (pr j).1
    · rw [if_pos hb]; exact hs hb
    · rw [if_neg hb]; have := hx hb; linarith
  have hprod : h ^ A.card * c ^ B.card ≤ ∏ i ∈ Finset.Iio j, (muh h j - muh h i) := by
    calc h ^ A.card * c ^ B.card = ∏ i ∈ Finset.Iio j, (if (pr i).1 = (pr j).1 then h else c) := by
          rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      _ ≤ ∏ i ∈ Finset.Iio j, (muh h j - muh h i) :=
          Finset.prod_le_prod₀ (fun i _ => by split_ifs <;> positivity) hfac
  have hAc : A.card ≤ ((pr j).2 : ℕ) := card_same_le j
  have hBc : B.card ≤ (j : ℕ) := by
    calc B.card ≤ (Finset.Iio j).card := Finset.card_filter_le _ _
      _ = j := Fin.card_Iio j
  calc h ^ ((pr j).2 : ℕ) * c ^ (j : ℕ) ≤ h ^ A.card * c ^ B.card := by
        apply mul_le_mul (pow_le_pow_of_le_one hh.le h1 hAc) (pow_le_pow_of_le_one hc0.le hc1 hBc)
          (by positivity) (by positivity)
    _ ≤ _ := hprod

/-! ## The two bounds for `D` -/

theorem eventually_small : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h ≤ 1 ∧ (K : ℝ) * h ≤ Real.log 2 / 2 := by
  have hlog : 0 < Real.log 2 / 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have h1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  have h2 : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < min 1 ((Real.log 2 / 2) / (K + 1)) :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by positivity))
  filter_upwards [h1, h2] with h ha hb
  refine ⟨ha, le_of_lt (lt_of_lt_of_le hb (min_le_left _ _)), ?_⟩
  have hb' : h < (Real.log 2 / 2) / (K + 1) := lt_of_lt_of_le hb (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hb'
  nlinarith

theorem tendsto_Wd_right (ζ : Fin (L * (K + 1)) → ℝ) (x : ℝ) :
    Tendsto (fun h => Wd ζ h x) (𝓝[>] 0) (𝓝 (Dc ζ x)) :=
  (tendsto_Wd ζ x).mono_left (nhdsGT_le_nhdsNE 0)

variable {ζ : Fin (L * (K + 1)) → ℝ}

/-- **Lower bound for `D(1)`.** -/
theorem abs_Dc_ge (hζ : Function.Injective ζ) (hζp : ∀ j, 0 < ζ j) :
    (∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) * (Real.log 2 / 2) ^ tri (L * (K + 1)) * |vprod ζ| ≤
      |Dc ζ 1| := by
  refine ge_of_tendsto (tendsto_Wd_right ζ 1).abs ?_
  filter_upwards [eventually_small (K := K)] with h ⟨hh, h1, hK⟩
  have hlog : Real.log 2 / 2 ≤ Real.log 2 := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  have hmono := muh_strictMono (L := L) (K := K) hh (by nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)])
  have hE := abs_det_Ek_ge hmono.injective (muh_pos hh.le) hζ hζp
  rw [conf_factor ζ hh.ne' 1, abs_mul (h ^ sig L K), abs_of_pos (by positivity : (0:ℝ) < h ^ sig L K)] at hE
  have hV := vprod_muh_ge (L := L) (K := K) hh h1 hK
  have hσ : (0 : ℝ) < h ^ sig L K := by positivity
  have hVpos : 0 ≤ vprod (muh (L := L) (K := K) h) := le_trans (by positivity) hV
  have hfac : (0 : ℝ) ≤ ∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ)) := Finset.prod_nonneg fun k _ => by positivity
  rw [abs_mul (vprod (muh h)), abs_of_nonneg hVpos] at hE
  -- divide by `h^σ`
  have key : h ^ sig L K * ((∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) *
      (Real.log 2 / 2) ^ tri (L * (K + 1)) * |vprod ζ|) ≤ h ^ sig L K * |Wd ζ h 1| := by
    calc h ^ sig L K * ((∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) *
          (Real.log 2 / 2) ^ tri (L * (K + 1)) * |vprod ζ|)
        = (∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) *
          (h ^ sig L K * (Real.log 2 / 2) ^ tri (L * (K + 1))) * |vprod ζ| := by ring
      _ ≤ (∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) * vprod (muh h) * |vprod ζ| := by gcongr
      _ ≤ h ^ sig L K * |Wd ζ h 1| := by rw [mul_assoc]; exact hE
  exact le_of_mul_le_mul_left key hσ

/-- **Schwarz-type upper bound for `D(1)`.** -/
theorem abs_Dc_le (hζ : Function.Injective ζ) (hζp : ∀ j, 0 < ζ j) {x : ℝ} (hx : 1 ≤ x) :
    |Dc ζ 1| ≤ (x ^ tri (L * (K + 1)))⁻¹ * |Dc ζ x| := by
  refine le_of_tendsto_of_tendsto (tendsto_Wd_right ζ 1).abs
    (((tendsto_Wd_right ζ x).abs).const_mul _) ?_
  filter_upwards [eventually_small (K := K)] with h ⟨hh, h1, hK⟩
  have hmono := muh_strictMono (L := L) (K := K) hh (by nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)])
  have hE := abs_det_Ek_le hmono.injective (muh_pos hh.le) hζ hζp hx
  rw [conf_factor ζ hh.ne' 1, conf_factor ζ hh.ne' x, abs_mul (h ^ sig L K), abs_mul (h ^ sig L K),
    abs_of_pos (by positivity : (0:ℝ) < h ^ sig L K)] at hE
  have hσ : (0 : ℝ) < h ^ sig L K := by positivity
  have : h ^ sig L K * |Wd ζ h 1| ≤ h ^ sig L K * ((x ^ tri (L * (K + 1)))⁻¹ * |Wd ζ h x|) := by
    calc h ^ sig L K * |Wd ζ h 1| ≤ (x ^ tri (L * (K + 1)))⁻¹ * (h ^ sig L K * |Wd ζ h x|) := hE
      _ = h ^ sig L K * ((x ^ tri (L * (K + 1)))⁻¹ * |Wd ζ h x|) := by ring
  exact le_of_mul_le_mul_left this hσ

end

end Logs23
