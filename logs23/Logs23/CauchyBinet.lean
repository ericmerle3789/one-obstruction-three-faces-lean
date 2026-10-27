import Mathlib

/-!
# Logs23 · the Cauchy–Binet formula

`det (A * B) = ∑_Q det (A with the columns in Q) · det (B with the rows in Q)`, for `A : N × n`, `B : n × N`,
`Q` ranging over the `N`-element subsets of `Fin n`, listed in increasing order by `Finset.orderEmbOfFin`.
-/

namespace Logs23

open Matrix Finset Equiv

variable {R : Type*} [CommRing R]

/-- The `N`-element subsets of `Fin n`. -/
abbrev Subsets (N n : ℕ) := {Q : Finset (Fin n) // Q.card = N}

/-- The increasing enumeration of `Q`. -/
abbrev enum {N n : ℕ} (Q : Subsets N n) : Fin N → Fin n := fun i => Q.1.orderEmbOfFin Q.2 i

/-- `det (A * B)` as a sum over all maps `Fin N → Fin n`. -/
theorem det_mul_eq_sum_fun {N n : ℕ} (A : Matrix (Fin N) (Fin n) R) (B : Matrix (Fin n) (Fin N) R) :
    (A * B).det = ∑ f : Fin N → Fin n, (A.submatrix id f).det * ∏ j, B (f j) j := by
  simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

theorem det_submatrix_eq_zero_of_not_injective {N n : ℕ} (A : Matrix (Fin N) (Fin n) R)
    {f : Fin N → Fin n} (hf : ¬ Function.Injective f) : (A.submatrix id f).det = 0 := by
  rw [Function.Injective] at hf
  push Not at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  exact det_zero_of_column_eq hne (fun k => by simp [hij])

theorem enum_injective {N n : ℕ} (Q : Subsets N n) : Function.Injective (enum Q) :=
  (Q.1.orderEmbOfFin Q.2).injective

theorem range_enum {N n : ℕ} (Q : Subsets N n) : Set.range (enum Q) = Q.1 :=
  Finset.range_orderEmbOfFin Q.1 Q.2

/-- **Cauchy–Binet.** -/
theorem det_mul_eq_sum_subsets {N n : ℕ} (A : Matrix (Fin N) (Fin n) R) (B : Matrix (Fin n) (Fin N) R) :
    (A * B).det = ∑ Q : Subsets N n, (A.submatrix id (enum Q)).det * (B.submatrix (enum Q) id).det := by
  set F : (Fin N → Fin n) → R := fun f => (A.submatrix id f).det * ∏ j, B (f j) j with hF
  -- the right side as a sum over pairs `(Q, σ)`
  have hR : ∀ Q : Subsets N n, (A.submatrix id (enum Q)).det * (B.submatrix (enum Q) id).det =
      ∑ σ : Perm (Fin N), F (enum Q ∘ σ) := by
    intro Q
    rw [det_apply' (B.submatrix (enum Q) id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 : A.submatrix id (enum Q ∘ σ) = (A.submatrix id (enum Q)).submatrix id σ := by
      ext i j; simp
    simp only [hF, h1, det_permute', submatrix_apply, id, Function.comp]
    ring
  rw [det_mul_eq_sum_fun, Finset.sum_congr rfl (fun Q _ => hR Q), ← Finset.sum_product']
  -- only injective maps contribute
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun f _ hf => by
    by_contra hinj
    exact hf (by simp [det_submatrix_eq_zero_of_not_injective A hinj]))]
  symm
  refine Finset.sum_bij (fun p _ => enum p.1 ∘ p.2) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (enum_injective p.1).comp p.2.injective
  · intro p _ q _ hpq
    have hQ : p.1 = q.1 := by
      apply Subtype.ext
      have := congrArg Set.range hpq
      simp only [Set.range_comp, Equiv.range_eq_univ, Set.image_univ] at this
      rw [range_enum, range_enum] at this
      exact_mod_cast this
    obtain ⟨Qp, σp⟩ := p
    obtain ⟨Qq, σq⟩ := q
    simp only at hQ
    subst hQ
    simp only [Prod.mk.injEq, true_and]
    ext i
    exact congrArg Fin.val (enum_injective Qp (congrFun hpq i))
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hcard : (Finset.univ.image f).card = N := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    set Q : Subsets N n := ⟨Finset.univ.image f, hcard⟩ with hQ
    have hmem : ∀ j, f j ∈ Q.1 := fun j => Finset.mem_image_of_mem f (Finset.mem_univ j)
    let τ : Fin N → Fin N := fun j => (Q.1.orderIsoOfFin Q.2).symm ⟨f j, hmem j⟩
    have hτ : ∀ j, enum Q (τ j) = f j := by
      intro j
      simp only [enum, τ]
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    have hτinj : Function.Injective τ := by
      intro a b hab
      apply hf
      rw [← hτ a, ← hτ b, hab]
    let σ : Perm (Fin N) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
    refine ⟨(Q, σ), Finset.mem_univ _, ?_⟩
    funext j
    exact hτ j
  · intro p _
    rfl

end Logs23
