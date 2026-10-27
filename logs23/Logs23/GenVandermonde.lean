import Mathlib

/-!
# Logs23 · generalized Vandermonde determinants

For `0 < y_1 < … < y_N` and natural numbers `m_1 < … < m_N`, `det [y_j ^ m_k] > 0`.
Non-vanishing comes from Descartes' rule of signs (`Polynomial.roots_countP_pos_le_signVariations`): a nonzero
polynomial with at most `N` nonzero coefficients has at most `N − 1` positive roots. The sign is then constant on the
convex set of increasing positive tuples, and positive at `y_j = 2^(j+1)` (a Vandermonde determinant).
-/

namespace Logs23

open Matrix Finset Polynomial

/-- The number of sign variations of a list is at most its number of nonzero entries minus one. -/
theorem List.signVariations_le_length_filter (l : List ℝ) :
    l.signVariations ≤ (l.filter (· ≠ 0)).length - 1 := by
  unfold List.signVariations
  apply Nat.sub_le_sub_right
  refine ((List.destutter_sublist _ _).length_le).trans (le_of_eq ?_)
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp [sign_eq_zero_iff]

/-- A polynomial whose nonzero coefficients sit in `s` has at most `s.card − 1` sign variations. -/
theorem signVariations_le_of_support_subset (P : ℝ[X]) {s : Finset ℕ} (hs : P.support ⊆ s) :
    P.signVariations ≤ s.card - 1 := by
  refine (List.signVariations_le_length_filter _).trans (Nat.sub_le_sub_right ?_ 1)
  unfold Polynomial.coeffList
  rw [List.filter_map, List.length_map]
  set F := (List.range P.degree.succ).reverse.filter ((· ≠ 0) ∘ P.coeff) with hF
  have hnd : F.Nodup := by
    rw [hF]
    exact (List.nodup_reverse.mpr List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro i hi
  rw [List.mem_toFinset, hF, List.mem_filter] at hi
  apply hs
  rw [Polynomial.mem_support_iff]
  simpa using hi.2

/-- Generalized Vandermonde determinants with distinct positive nodes and distinct exponents do not vanish. -/
theorem det_genVandermonde_ne_zero {N : ℕ} {y : Fin N → ℝ} (hy : Function.Injective y) (hpos : ∀ j, 0 < y j)
    {m : Fin N → ℕ} (hm : Function.Injective m) : (Matrix.of fun k j => y j ^ m k).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hcM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  set P : ℝ[X] := ∑ k, C (c k) * X ^ (m k) with hP
  have hcoeff : ∀ k, P.coeff (m k) = c k := by
    intro k
    rw [hP, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      have : m k ≠ m b := fun h => hb (hm h).symm
      simp [this]
    · simp
  have hsupp : P.support ⊆ Finset.univ.image m := by
    intro i hi
    rw [Polynomial.mem_support_iff, hP, Polynomial.finsetSum_coeff] at hi
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    rw [Polynomial.coeff_C_mul_X_pow] at hk
    by_cases hik : i = m k
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hik.symm⟩
    · simp [hik] at hk
  have hPne : P ≠ 0 := by
    intro hP0
    apply hc
    funext k
    rw [← hcoeff k, hP0, Polynomial.coeff_zero, Pi.zero_apply]
  have heval : ∀ j, P.IsRoot (y j) := by
    intro j
    have h := congrFun hcM j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
    rw [Polynomial.IsRoot, hP, Polynomial.eval_finsetSum]
    simpa using h
  -- `N` distinct positive roots
  have hle : (Finset.univ.val.map y) ≤ P.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hy Finset.univ.nodup)]
    intro x hx
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hPne).mpr (heval j)
  have hcount : N ≤ P.roots.countP (0 < ·) := by
    calc N = (Finset.univ.val.map y).countP (0 < ·) := by
          rw [Multiset.countP_eq_card.mpr (fun x hx => by
            obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hx
            exact hpos j)]
          simp
      _ ≤ P.roots.countP (0 < ·) := Multiset.countP_le_of_le _ hle
  have hsv := signVariations_le_of_support_subset P hsupp
  have hcard : (Finset.univ.image m).card ≤ N := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := m)
  have hdesc := Polynomial.roots_countP_pos_le_signVariations P
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact absurd (_root_.funext fun k => Fin.elim0 k) hc
    · exact h
  omega

/-- The value at the reference nodes `y_j = 2^(j+1)`. -/
theorem det_genVandermonde_ref_pos {N : ℕ} {m : Fin N → ℕ} (hm : StrictMono m) :
    0 < (Matrix.of fun k (j : Fin N) => ((2 : ℝ) ^ (j.1 + 1)) ^ m k).det := by
  set u : Fin N → ℝ := fun k => (2 : ℝ) ^ m k with hu
  have hmat : (Matrix.of fun k (j : Fin N) => ((2 : ℝ) ^ (j.1 + 1)) ^ m k) =
      Matrix.of fun k j => u k * Matrix.vandermonde u k j := by
    ext k j
    simp only [Matrix.of_apply, Matrix.vandermonde_apply, hu, ← pow_mul]
    ring_nf
  rw [hmat, Matrix.det_mul_column, Matrix.det_vandermonde]
  have hus : StrictMono u := fun a b hab => pow_lt_pow_right₀ (by norm_num) (hm hab)
  apply mul_pos
  · exact Finset.prod_pos fun k _ => by positivity
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have : i < j := Finset.mem_Ioi.mp hj
    linarith [hus this]

/-- **Generalized Vandermonde determinants are positive** for increasing positive nodes and increasing exponents. -/
theorem det_genVandermonde_pos {N : ℕ} {y : Fin N → ℝ} (hy : StrictMono y) (hpos : ∀ j, 0 < y j)
    {m : Fin N → ℕ} (hm : StrictMono m) : 0 < (Matrix.of fun k j => y j ^ m k).det := by
  set y₀ : Fin N → ℝ := fun j => (2 : ℝ) ^ (j.1 + 1) with hy₀
  have hy₀s : StrictMono y₀ := fun a b hab => pow_lt_pow_right₀ (by norm_num) (by simpa using hab)
  set z : ℝ → Fin N → ℝ := fun t j => (1 - t) * y₀ j + t * y j with hz
  set g : ℝ → ℝ := fun t => (Matrix.of fun k j => z t j ^ m k).det with hg
  have hzs : ∀ t ∈ Set.Icc (0 : ℝ) 1, StrictMono (z t) ∧ ∀ j, 0 < z t j := by
    intro t ht
    obtain ⟨h0, h1⟩ := ht
    refine ⟨fun a b hab => ?_, fun j => ?_⟩
    · have ha := hy₀s hab
      have hb := hy hab
      simp only [hz]
      rcases eq_or_lt_of_le h0 with rfl | h0'
      · simpa using ha
      · nlinarith
    · have : 0 < y₀ j := by positivity
      simp only [hz]
      rcases eq_or_lt_of_le h1 with rfl | h1'
      · simpa using hpos j
      · nlinarith [hpos j]
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ≠ 0 := fun t ht =>
    det_genVandermonde_ne_zero (hzs t ht).1.injective (hzs t ht).2 hm.injective
  have hcont : Continuous g := by
    apply Continuous.matrix_det
    refine continuous_pi fun k => continuous_pi fun j => ?_
    simp only [hz, Matrix.of_apply]
    fun_prop
  have hg0 : 0 < g 0 := by
    simpa [hg, hz] using det_genVandermonde_ref_pos hm
  have hg1 : g 1 = (Matrix.of fun k j => y j ^ m k).det := by simp [hg, hz]
  rw [← hg1]
  by_contra hneg
  rw [not_lt] at hneg
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont.continuousOn ⟨hneg, hg0.le⟩
  exact hne t ht hgt

end Logs23
