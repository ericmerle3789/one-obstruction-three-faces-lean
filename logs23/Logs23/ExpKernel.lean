import Mathlib
import Logs23.CauchyBinet
import Logs23.GenVandermonde

/-!
# Logs23 · the exponential kernel `det [exp (μ_i ζ_j)]`

For distinct positive `μ_i` and distinct positive `ζ_j`, the Cauchy–Binet expansion of `det [exp (μ_i x ζ_j)]`
(truncated exponential series, then `n → ∞`) has all its terms of the same sign (generalized Vandermonde
determinants). Hence
* `|det [exp (μ_i ζ_j)]| ≥ (∏_{m<N} 1/m!) |V(μ)| |V(ζ)|` (one term);
* `|det [exp (μ_i ζ_j)]| ≤ x^(−∑_{k<N} k) |det [exp (μ_i x ζ_j)]|` for `x ≥ 1` (termwise).
-/

namespace Logs23

open Matrix Finset Filter Topology Equiv
open scoped Nat

noncomputable section

/-- The Vandermonde product `∏_{i<j} (v_j − v_i)`. -/
def vprod {N : ℕ} (v : Fin N → ℝ) : ℝ := ∏ i : Fin N, ∏ j ∈ Ioi i, (v j - v i)

/-- `0 + 1 + ⋯ + (N − 1)`. -/
def tri (N : ℕ) : ℕ := ∑ k : Fin N, (k : ℕ)

/-- The sum of the elements of `Q`. -/
def esum {N n : ℕ} (Q : Subsets N n) : ℕ := ∑ k, (enum Q k : ℕ)

theorem val_le_of_strictMono {N n : ℕ} {f : Fin N → Fin n} (hf : StrictMono f) (k : Fin N) :
    (k : ℕ) ≤ f k := by
  obtain ⟨k, hk⟩ := k
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨k, by omega⟩ < f ⟨k + 1, hk⟩ := hf (Fin.mk_lt_mk.mpr (by omega))
    have : ((f ⟨k, by omega⟩ : Fin n) : ℕ) < f ⟨k + 1, hk⟩ := h2
    simp only at h1 ⊢
    omega

theorem tri_le_esum {N n : ℕ} (Q : Subsets N n) : tri N ≤ esum Q :=
  Finset.sum_le_sum fun k _ => val_le_of_strictMono (Q.1.orderEmbOfFin Q.2).strictMono k

/-- Sign of a generalized Vandermonde determinant with distinct positive nodes: that of the permutation sorting
the nodes, for every increasing family of exponents. -/
theorem sign_mul_det_genVandermonde_pos {N : ℕ} {y : Fin N → ℝ} (hy : Function.Injective y)
    (hpos : ∀ j, 0 < y j) {e : Fin N → ℕ} (he : StrictMono e) :
    0 < ((Perm.sign (Tuple.sort y) : ℤ) : ℝ) * (Matrix.of fun k j => y j ^ e k).det := by
  set σ := Tuple.sort y
  have hmono : StrictMono (y ∘ σ) :=
    (Tuple.monotone_sort y).strictMono_of_injective (hy.comp σ.injective)
  have h := det_genVandermonde_pos hmono (fun j => hpos (σ j)) he
  have hsub : (Matrix.of fun k j => (y ∘ σ) j ^ e k) = (Matrix.of fun k j => y j ^ e k).submatrix id σ := by
    ext k j; simp
  rw [hsub, det_permute'] at h
  simpa using h

/-- The truncated matrices. -/
def Atr {N : ℕ} (μ : Fin N → ℝ) (n : ℕ) : Matrix (Fin N) (Fin n) ℝ := Matrix.of fun i m => μ i ^ (m : ℕ) / (m : ℕ)!

def Btr {N : ℕ} (ζ : Fin N → ℝ) (x : ℝ) (n : ℕ) : Matrix (Fin n) (Fin N) ℝ :=
  Matrix.of fun m j => (x * ζ j) ^ (m : ℕ)

/-- The kernel matrix. -/
def Ek {N : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => Real.exp (μ i * (x * ζ j))

theorem tendsto_Atr_mul_Btr {N : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) :
    Tendsto (fun n => Atr μ n * Btr ζ x n) atTop (𝓝 (Ek μ ζ x)) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have hs : HasSum (fun m : ℕ => (μ i * (x * ζ j)) ^ m / (m)!) (Real.exp (μ i * (x * ζ j))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have h := hs.tendsto_sum_nat
  refine h.congr fun n => ?_
  simp only [Matrix.mul_apply, Atr, Btr, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun m => μ i ^ m / (m)! * (x * ζ j) ^ m) n]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow]; ring

theorem tendsto_det {N : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) :
    Tendsto (fun n => (Atr μ n * Btr ζ x n).det) atTop (𝓝 (Ek μ ζ x).det) :=
  ((continuous_id.matrix_det).tendsto _).comp (tendsto_Atr_mul_Btr μ ζ x)

/-- The terms of the Cauchy–Binet expansion. -/
def term {N n : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) (Q : Subsets N n) : ℝ :=
  ((Atr μ n).submatrix id (enum Q)).det * ((Btr ζ x n).submatrix (enum Q) id).det

theorem term_eq {N n : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) (Q : Subsets N n) :
    term μ ζ x Q = (∏ k, (1 / ((enum Q k : ℕ)! : ℝ))) * x ^ esum Q *
      ((Matrix.of fun k i => μ i ^ (enum Q k : ℕ)).det * (Matrix.of fun k j => ζ j ^ (enum Q k : ℕ)).det) := by
  have hA : (Atr μ n).submatrix id (enum Q) =
      Matrix.of fun i k => (1 / ((enum Q k : ℕ)! : ℝ)) * (Matrix.of fun k i => μ i ^ (enum Q k : ℕ))ᵀ i k := by
    ext i k; simp [Atr, div_eq_inv_mul]
  have hB : (Btr ζ x n).submatrix (enum Q) id =
      Matrix.of fun k j => x ^ (enum Q k : ℕ) * (Matrix.of fun k j => ζ j ^ (enum Q k : ℕ)) k j := by
    ext k j; simp [Btr, mul_pow]
  rw [term, hA, hB, det_mul_row, det_mul_column, det_transpose, esum, Finset.prod_pow_eq_pow_sum]
  ring

/-- All terms have the sign `ε := sign(sort μ) · sign(sort ζ)`. -/
theorem eps_mul_term_nonneg {N n : ℕ} {μ ζ : Fin N → ℝ} (hμ : Function.Injective μ) (hμp : ∀ i, 0 < μ i)
    (hζ : Function.Injective ζ) (hζp : ∀ j, 0 < ζ j) {x : ℝ} (hx : 0 ≤ x) (Q : Subsets N n) :
    0 ≤ ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) * term μ ζ x Q := by
  have he : StrictMono (fun k => (enum Q k : ℕ)) := fun a b hab =>
    (Q.1.orderEmbOfFin Q.2).strictMono hab
  have h1 := sign_mul_det_genVandermonde_pos hμ hμp he
  have h2 := sign_mul_det_genVandermonde_pos hζ hζp he
  have h3 : 0 ≤ (∏ k, (1 / ((enum Q k : ℕ)! : ℝ))) * x ^ esum Q :=
    mul_nonneg (Finset.prod_nonneg fun k _ => by positivity) (pow_nonneg hx _)
  rw [term_eq]
  have : ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) *
      ((∏ k, (1 / ((enum Q k : ℕ)! : ℝ))) * x ^ esum Q *
        ((Matrix.of fun k i => μ i ^ (enum Q k : ℕ)).det * (Matrix.of fun k j => ζ j ^ (enum Q k : ℕ)).det)) =
      ((∏ k, (1 / ((enum Q k : ℕ)! : ℝ))) * x ^ esum Q) *
        ((((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * (Matrix.of fun k i => μ i ^ (enum Q k : ℕ)).det) *
          (((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) * (Matrix.of fun k j => ζ j ^ (enum Q k : ℕ)).det)) := by ring
  rw [this]
  exact mul_nonneg h3 (mul_pos h1 h2).le

theorem term_scale {N n : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) (Q : Subsets N n) :
    term μ ζ x Q = x ^ esum Q * term μ ζ 1 Q := by
  rw [term_eq, term_eq, one_pow]; ring

/-- The leading subset `{0, …, N − 1}` of `Fin n`, `N ≤ n`. -/
def Q₀ {N n : ℕ} (h : N ≤ n) : Subsets N n :=
  ⟨Finset.univ.map (Fin.castLEEmb h), by simp⟩

theorem enum_Q₀ {N n : ℕ} (h : N ≤ n) (k : Fin N) : enum (Q₀ h) k = Fin.castLE h k := by
  have := Finset.orderEmbOfFin_unique (Q₀ h).2 (f := Fin.castLE h)
    (fun k => by simp [Q₀]) (Fin.strictMono_castLE h)
  exact (congrFun this k).symm

theorem vprod_eq_det {N : ℕ} (v : Fin N → ℝ) : (Matrix.of fun (k : Fin N) j => v j ^ (k : ℕ)).det = vprod v := by
  rw [vprod, ← Matrix.det_vandermonde, ← det_transpose]
  rfl

theorem term_Q₀ {N n : ℕ} (h : N ≤ n) (μ ζ : Fin N → ℝ) :
    term μ ζ 1 (Q₀ h) = (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * (vprod μ * vprod ζ) := by
  rw [term_eq]
  simp only [enum_Q₀, Fin.val_castLE, one_pow, mul_one]
  rw [vprod_eq_det ζ, ← vprod_eq_det μ]

/-- `ε · det(truncated product) = Σ ε · term`, a sum of nonnegative terms. -/
theorem eps_det_trunc {N n : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) (ε : ℝ) :
    ε * (Atr μ n * Btr ζ x n).det = ∑ Q : Subsets N n, ε * term μ ζ x Q := by
  rw [det_mul_eq_sum_subsets, Finset.mul_sum]; rfl

variable {N : ℕ} {μ ζ : Fin N → ℝ}

theorem eps_det_Ek_ge (hμ : Function.Injective μ) (hμp : ∀ i, 0 < μ i) (hζ : Function.Injective ζ)
    (hζp : ∀ j, 0 < ζ j) :
    (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * |vprod μ * vprod ζ| ≤
      ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) * (Ek μ ζ 1).det := by
  set ε := ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) with hε
  have hεabs : |ε| = 1 := by
    rw [hε, abs_mul]
    rcases Int.units_eq_one_or (Perm.sign (Tuple.sort μ)) with h | h <;>
    rcases Int.units_eq_one_or (Perm.sign (Tuple.sort ζ)) with h' | h' <;> simp [h, h']
  have hlim := (tendsto_det μ ζ 1).const_mul ε
  refine ge_of_tendsto hlim (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
  rw [eps_det_trunc]
  have hQ₀ := Finset.single_le_sum (f := fun Q => ε * term μ ζ 1 Q)
    (fun Q _ => eps_mul_term_nonneg hμ hμp hζ hζp zero_le_one Q) (Finset.mem_univ (Q₀ hn))
  refine le_trans (le_of_eq ?_) hQ₀
  have hpos : 0 ≤ ε * term μ ζ 1 (Q₀ hn) := eps_mul_term_nonneg hμ hμp hζ hζp zero_le_one _
  set c : ℝ := ∏ k : Fin N, (1 / ((k : ℕ)! : ℝ)) with hc
  have hc0 : 0 ≤ c := Finset.prod_nonneg fun k _ => by positivity
  have ht : term μ ζ 1 (Q₀ hn) = c * (vprod μ * vprod ζ) := term_Q₀ hn μ ζ
  calc c * |vprod μ * vprod ζ| = |ε| * (|c| * |vprod μ * vprod ζ|) := by
        rw [hεabs, abs_of_nonneg hc0, one_mul]
    _ = |ε * term μ ζ 1 (Q₀ hn)| := by rw [ht, abs_mul ε (c * _), abs_mul c]
    _ = ε * term μ ζ 1 (Q₀ hn) := abs_of_nonneg hpos

/-- **The lower bound.** -/
theorem abs_det_Ek_ge (hμ : Function.Injective μ) (hμp : ∀ i, 0 < μ i) (hζ : Function.Injective ζ)
    (hζp : ∀ j, 0 < ζ j) :
    (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * |vprod μ * vprod ζ| ≤ |(Ek μ ζ 1).det| := by
  refine (eps_det_Ek_ge hμ hμp hζ hζp).trans ?_
  refine (le_abs_self _).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul]
  rcases Int.units_eq_one_or (Perm.sign (Tuple.sort μ)) with h | h <;>
  rcases Int.units_eq_one_or (Perm.sign (Tuple.sort ζ)) with h' | h' <;> simp [h, h']

/-- **The Schwarz-type upper bound.** -/
theorem abs_det_Ek_le (hμ : Function.Injective μ) (hμp : ∀ i, 0 < μ i) (hζ : Function.Injective ζ)
    (hζp : ∀ j, 0 < ζ j) {x : ℝ} (hx : 1 ≤ x) :
    |(Ek μ ζ 1).det| ≤ (x ^ tri N)⁻¹ * |(Ek μ ζ x).det| := by
  set ε := ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) with hε
  have hεabs : |ε| = 1 := by
    rw [hε, abs_mul]
    rcases Int.units_eq_one_or (Perm.sign (Tuple.sort μ)) with h | h <;>
    rcases Int.units_eq_one_or (Perm.sign (Tuple.sort ζ)) with h' | h' <;> simp [h, h']
  have hx0 : 0 < x := by linarith
  -- termwise comparison, then limit
  have hfin : ∀ n, ε * (Atr μ n * Btr ζ 1 n).det ≤ (x ^ tri N)⁻¹ * (ε * (Atr μ n * Btr ζ x n).det) := by
    intro n
    rw [eps_det_trunc, eps_det_trunc, Finset.mul_sum]
    refine Finset.sum_le_sum fun Q _ => ?_
    have hnn := eps_mul_term_nonneg hμ hμp hζ hζp zero_le_one Q
    rw [term_scale μ ζ x Q]
    have hpow : x ^ tri N ≤ x ^ esum Q := pow_le_pow_right₀ hx (tri_le_esum Q)
    have hpos : 0 < x ^ tri N := by positivity
    calc ε * term μ ζ 1 Q = (x ^ tri N)⁻¹ * (x ^ tri N * (ε * term μ ζ 1 Q)) := by
          field_simp
      _ ≤ (x ^ tri N)⁻¹ * (x ^ esum Q * (ε * term μ ζ 1 Q)) := by
          gcongr
      _ = (x ^ tri N)⁻¹ * (ε * (x ^ esum Q * term μ ζ 1 Q)) := by ring
  have hlim1 := (tendsto_det μ ζ 1).const_mul ε
  have hlimx := ((tendsto_det μ ζ x).const_mul ε).const_mul (x ^ tri N)⁻¹
  have hle := le_of_tendsto_of_tendsto' hlim1 hlimx hfin
  have hnn : 0 ≤ ε * (Ek μ ζ 1).det :=
    le_trans (mul_nonneg (Finset.prod_nonneg fun k _ => by positivity) (abs_nonneg _))
      (eps_det_Ek_ge hμ hμp hζ hζp)
  calc |(Ek μ ζ 1).det| = ε * (Ek μ ζ 1).det := by
        rw [← abs_of_nonneg hnn, abs_mul, hεabs, one_mul]
    _ ≤ (x ^ tri N)⁻¹ * (ε * (Ek μ ζ x).det) := hle
    _ ≤ (x ^ tri N)⁻¹ * |(Ek μ ζ x).det| := by
        gcongr
        calc ε * (Ek μ ζ x).det ≤ |ε * (Ek μ ζ x).det| := le_abs_self _
          _ = |(Ek μ ζ x).det| := by rw [abs_mul, hεabs, one_mul]

end

end Logs23
