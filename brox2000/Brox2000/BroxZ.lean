import Mathlib
import Brox2000.BroxZ_Enonces
import Brox2000.Brox
import Brox2000.MiroirChaine
import Brox2000.MiroirCycles
import Brox2000.MiroirCombinatoire

/-!
# Brox 2000 · proofs of the frozen statements of phase B (`Brox2000/BroxZ_Enonces.lean`)

`T (n : ℤ) = C n` and `T (−n) = −D n` for `n : ℕ` (`C = Sdw2005.C`, `D = Brox2000.Miroir.D`), so `n ↦ n` and
`n ↦ −n` carry the cycles of `C` and of `D` onto the cycles of `T` on the positive and on the negative integers, with
the same minimal period, the same `Γ` and the same descending elements. On the positive side, phase A
(`Brox2000/Brox.lean`) applies. On the negative side: the cycle `{1}` of `D` (Brox's fixed point `−1`) has
`|Γ| = 1`; a cycle through `n > 1` gives a solution of the mirrored chain equation (`Miroir.cycle_chainM`) with
`m = δ(Γ)` blocks and `K = |Γ|` odd steps, and `Miroir.chain_K_lt_brox_M` concludes as in phase A. The cycle `{0}` has
no odd element.
-/

namespace Brox2000

open Sdw2005 Miroir

/-! ## Conjugacies -/

theorem T_natCast (n : ℕ) : T (n : ℤ) = (C n : ℤ) := by
  unfold T C; split_ifs <;> omega

theorem T_negCast (n : ℕ) : T (-(n : ℤ)) = -(D n : ℤ) := by
  unfold T D; split_ifs <;> omega

theorem iterate_natCast (n j : ℕ) : T^[j] (n : ℤ) = (C^[j] n : ℤ) :=
  ((Function.Semiconj.iterate_right (f := fun n : ℕ => (n : ℤ)) (fun x => (T_natCast x).symm) j) n).symm

theorem iterate_negCast (n j : ℕ) : T^[j] (-(n : ℤ)) = -(D^[j] n : ℤ) :=
  ((Function.Semiconj.iterate_right (f := fun n : ℕ => -(n : ℤ)) (fun x => (T_negCast x).symm) j) n).symm

theorem mp_natCast (n : ℕ) : Function.minimalPeriod T (n : ℤ) = Function.minimalPeriod C n := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro j
  unfold Function.IsPeriodicPt Function.IsFixedPt
  rw [iterate_natCast]
  exact Nat.cast_inj

theorem mp_negCast (n : ℕ) : Function.minimalPeriod T (-(n : ℤ)) = Function.minimalPeriod D n := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro j
  unfold Function.IsPeriodicPt Function.IsFixedPt
  rw [iterate_negCast, neg_inj]
  exact Nat.cast_inj

theorem negCast_injective : Function.Injective (fun x : ℕ => -(x : ℤ)) := by
  intro a b h
  simpa using h

/-! ## `Γ` and the descending elements under the conjugacies -/

theorem GammaZ_natCast (n : ℕ) : GammaZ (n : ℤ) = (Gamma n).image (fun x : ℕ => (x : ℤ)) := by
  ext y
  simp only [GammaZ, Gamma, oddValues, orbitSet, mp_natCast, iterate_natCast, Finset.mem_filter,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hy⟩
    exact ⟨C^[j] n, ⟨⟨j, hj, rfl⟩, by omega⟩, rfl⟩
  · rintro ⟨x, ⟨⟨j, hj, rfl⟩, hx⟩, rfl⟩
    exact ⟨⟨j, hj, rfl⟩, by omega⟩

theorem descSetZ_natCast (n : ℕ) : descSetZ (n : ℤ) = (descSet n).image (fun x : ℕ => (x : ℤ)) := by
  ext y
  simp only [descSetZ, descSet, GammaZ_natCast, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    rw [T_natCast] at h
    exact ⟨x, ⟨hx, by omega⟩, rfl⟩
  · rintro ⟨x, ⟨hx, h⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rw [T_natCast]; omega

theorem GammaZ_negCast (n : ℕ) : GammaZ (-(n : ℤ)) = (GammaD n).image (fun x : ℕ => -(x : ℤ)) := by
  ext y
  simp only [GammaZ, GammaD, mp_negCast, iterate_negCast, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hy⟩
    exact ⟨D^[j] n, ⟨⟨j, hj, rfl⟩, by omega⟩, rfl⟩
  · rintro ⟨x, ⟨⟨j, hj, rfl⟩, hx⟩, rfl⟩
    exact ⟨⟨j, hj, rfl⟩, by omega⟩

theorem descSetZ_negCast (n : ℕ) : descSetZ (-(n : ℤ)) = (descSetD n).image (fun x : ℕ => -(x : ℤ)) := by
  ext y
  simp only [descSetZ, descSetD, GammaZ_negCast, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    rw [T_negCast] at h
    exact ⟨x, ⟨hx, by omega⟩, rfl⟩
  · rintro ⟨x, ⟨hx, h⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rw [T_negCast]; omega

theorem GammaZ_natCast_card (n : ℕ) : (GammaZ (n : ℤ)).card = (Gamma n).card := by
  rw [GammaZ_natCast, Finset.card_image_of_injective _ Nat.cast_injective]

theorem descSetZ_natCast_card (n : ℕ) : (descSetZ (n : ℤ)).card = (descSet n).card := by
  rw [descSetZ_natCast, Finset.card_image_of_injective _ Nat.cast_injective]

theorem GammaZ_negCast_card (n : ℕ) : (GammaZ (-(n : ℤ))).card = (GammaD n).card := by
  rw [GammaZ_negCast, Finset.card_image_of_injective _ negCast_injective]

theorem descSetZ_negCast_card (n : ℕ) : (descSetZ (-(n : ℤ))).card = (descSetD n).card := by
  rw [descSetZ_negCast, Finset.card_image_of_injective _ negCast_injective]

/-- The cycle `{0}` has no odd element. -/
theorem GammaZ_zero_card : (GammaZ 0).card = 0 := by
  have h0 : ∀ j, T^[j] 0 = 0 := fun j => Function.iterate_fixed (by decide) j
  unfold GammaZ
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y hy
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
  rw [h0]; decide

/-- `|Γ|` is at most the period. -/
theorem GammaZ_card_le (x : ℤ) : (GammaZ x).card ≤ Function.minimalPeriod T x := by
  unfold GammaZ
  exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (Finset.card_range _).le)

/-! ## The negative side -/

theorem lemma22_finite_neg (K : ℕ) :
    Set.Finite {n : ℕ | 0 < n ∧ 0 < Function.minimalPeriod D n ∧ (GammaD n).card ≤ K} := by
  apply (Set.finite_Iic (2 * K * 3 ^ K * 2 ^ (2 * K))).subset
  rintro n ⟨hn, hp, hK⟩
  rw [Set.mem_Iic]
  have hc : D^[Function.minimalPeriod D n] n = n := Function.iterate_minimalPeriod
  have h1 := elem_leD hn hp hc
  rw [GammaD_card] at hK
  have h2 : Function.minimalPeriod D n ≤ 2 * K := (period_le_two_oddD hn hc).trans (by omega)
  calc n ≤ Function.minimalPeriod D n * 3 ^ oddCountD n (Function.minimalPeriod D n) *
        2 ^ Function.minimalPeriod D n := h1
    _ ≤ 2 * K * 3 ^ K * 2 ^ (2 * K) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul h2 (Nat.pow_le_pow_right (by norm_num) hK))
        (Nat.pow_le_pow_right (by norm_num) h2)

set_option exponentiation.threshold 2000 in
theorem thm11_neg_explicit {n : ℕ} (hn : 0 < n) (hp : 0 < Function.minimalPeriod D n)
    (hδ : ((descSetD n).card : ℝ) < 2 * Real.log ((GammaD n).card : ℝ)) : (GammaD n).card < 2 ^ 1500 := by
  have hc : D^[Function.minimalPeriod D n] n = n := Function.iterate_minimalPeriod
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · rw [descSetD_card, descCountD_eq_minCountD hp hc, GammaD_card] at hδ
    rw [GammaD_card]
    obtain ⟨k, l, a, hs, hK⟩ := cycle_chainM n _ hn1 hp hc
    rw [← hK] at hδ ⊢
    exact chain_K_lt_brox_M _ k l a hs hδ
  · -- `n = 1`: the fixed point `1` of `D`
    have h1 : n = 1 := by omega
    subst h1
    have hp1 : Function.minimalPeriod D 1 = 1 := Function.minimalPeriod_eq_one_iff_isFixedPt.2 D_one
    have : (GammaD 1).card ≤ 1 := by
      unfold GammaD
      rw [hp1]
      exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (Finset.card_range _).le)
    calc (GammaD 1).card ≤ 1 := this
      _ < 2 ^ 1500 := Nat.one_lt_two_pow (by norm_num)

/-! ## The frozen statements -/

theorem lemma22_Z_thm : lemma22_Z := by
  intro x hx hp
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · have hn : 0 < n := by omega
    rw [mp_natCast] at hp ⊢
    rw [GammaZ_natCast_card]
    exact lemma22_pos_thm n hn hp
  · have hn : 0 < n := by omega
    rw [mp_negCast] at hp ⊢
    rw [GammaZ_negCast_card, GammaD_card]
    exact period_le_two_oddD hn Function.iterate_minimalPeriod

theorem lemma22_finite_Z_thm : lemma22_finite_Z := by
  intro K
  have hP := (lemma22_finite_pos_thm K).image (fun n : ℕ => (n : ℤ))
  have hN := (lemma22_finite_neg K).image (fun n : ℕ => -(n : ℤ))
  apply ((hP.union hN).union (Set.finite_singleton (0 : ℤ))).subset
  rintro x ⟨hp, hK⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · rcases Nat.eq_zero_or_pos n with h0 | hn
    · right; simp [h0]
    · left; left
      rw [mp_natCast] at hp
      rw [GammaZ_natCast_card] at hK
      exact ⟨n, ⟨hn, hp, hK⟩, rfl⟩
  · rcases Nat.eq_zero_or_pos n with h0 | hn
    · right; simp [h0]
    · left; right
      rw [mp_negCast] at hp
      rw [GammaZ_negCast_card] at hK
      exact ⟨n, ⟨hn, hp, hK⟩, rfl⟩

theorem thm11_Z_explicit_thm : thm11_Z_explicit := by
  intro x hp hδ
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      have h := GammaZ_zero_card
      simp only [Nat.cast_zero] at hδ ⊢
      rw [h] at hδ
      norm_num at hδ
      exact absurd hδ (not_lt.2 (Nat.cast_nonneg _))
    · rw [mp_natCast] at hp
      rw [descSetZ_natCast_card, GammaZ_natCast_card] at hδ
      rw [GammaZ_natCast_card]
      exact thm11_pos_explicit_thm n hn hp hδ
  · rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      have h := GammaZ_zero_card
      simp only [Nat.cast_zero, neg_zero] at hδ ⊢
      rw [h] at hδ
      norm_num at hδ
      exact absurd hδ (not_lt.2 (Nat.cast_nonneg _))
    · rw [mp_negCast] at hp
      rw [descSetZ_negCast_card, GammaZ_negCast_card] at hδ
      rw [GammaZ_negCast_card]
      exact thm11_neg_explicit hn hp hδ

theorem thm11_Z_thm : thm11_Z := by
  apply (lemma22_finite_Z_thm (2 ^ 1500)).subset
  rintro x ⟨hp, hδ⟩
  exact ⟨hp, (thm11_Z_explicit_thm x hp hδ).le⟩

theorem cor12_Z_thm : cor12_Z := by
  intro ν
  apply (lemma22_finite_Z_thm (2 ^ 1500 + 3 ^ ν)).subset
  rintro x ⟨hp, hδ⟩
  refine ⟨hp, ?_⟩
  by_cases h : (ν : ℝ) < 2 * Real.log ((GammaZ x).card : ℝ)
  · have hδ' : ((descSetZ x).card : ℝ) < 2 * Real.log ((GammaZ x).card : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast hδ) h
    exact le_add_right (thm11_Z_explicit_thm x hp hδ').le
  · rw [not_lt] at h
    -- `|Γ| ≤ e^{ν/2} ≤ 3^ν`
    have hle : (GammaZ x).card ≤ 3 ^ ν := by
      rcases Nat.eq_zero_or_pos (GammaZ x).card with h0 | h0
      · rw [h0]; exact Nat.zero_le _
      have hr : (0 : ℝ) < (GammaZ x).card := by exact_mod_cast h0
      have h1 : ((GammaZ x).card : ℝ) ≤ Real.exp ν := by
        calc ((GammaZ x).card : ℝ) = Real.exp (Real.log (GammaZ x).card) := (Real.exp_log hr).symm
          _ ≤ Real.exp ν := Real.exp_le_exp.mpr (by
              have : 0 ≤ Real.log ((GammaZ x).card : ℝ) :=
                Real.log_nonneg (by exact_mod_cast h0)
              linarith)
      have h2 : Real.exp ν ≤ (3 : ℝ) ^ ν := by
        rw [show (ν : ℝ) = (ν : ℕ) * 1 by ring, Real.exp_nat_mul]
        exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) ν
      exact_mod_cast h1.trans h2
    exact le_add_left hle

end Brox2000
