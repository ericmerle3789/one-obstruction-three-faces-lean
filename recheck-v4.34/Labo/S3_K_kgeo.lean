import Labo.S3_Enonces
-- S3-A · A4 formaliste (2026-09-26) : copie signée de Labo/Tent_kgeo_P2.lean (sha16 2a852c82633962e7), re-jugée sous l'oracle.

/-!
# S3-A · prouveur P2 · node `kgeo` (B14, K-geo)
Idea: in `ZMod m`, `m = |2^N - a^r|`, take the root `t` of `kgeo_root` (`t^r = 2`, `t^N = a`);
by `kgeo_ring`, `ChrisSum a N r = t^{(N-1)(r-1)} · Σ_{s<r} t^s`; `t` is a unit (`t^r = 2`, `m` odd)
and `(Σ_{s<r} t^s)(t - 1) = t^r - 1 = 1`, so `ChrisSum` is a unit mod `m`, i.e. coprime to `m`.
Self-contained (the proofs of the two children are repeated in namespace `P2Kgeo`, so that
this file never clashes with the signed copies `S3_K_kgeo_ring` / `S3_K_kgeo_root`).
-/

namespace P2Kgeo
open LaboBP LaboK

theorem odd_coprime_two (x : ℤ) (hx : Odd x) : IsCoprime x 2 := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨1, -k, by rw [hk]; ring⟩

theorem cop_a (a N r : ℕ) (ha : Odd a) (hr : 1 ≤ r) :
    IsCoprime (a : ℤ) ((2 : ℤ) ^ N - (a : ℤ) ^ r) := by
  have ha' : Odd (a : ℤ) := by exact_mod_cast ha
  have h2 : IsCoprime (a : ℤ) ((2 : ℤ) ^ N) := (odd_coprime_two _ ha').pow_right
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have e : (2 : ℤ) ^ N - (a : ℤ) ^ (s + 1) = (2 : ℤ) ^ N + (a : ℤ) * (-(a : ℤ) ^ s) := by ring
  rw [e]; exact h2.add_mul_left_right _

theorem cop_two (a N r : ℕ) (ha : Odd a) (hN : 1 ≤ N) :
    IsCoprime (2 : ℤ) ((2 : ℤ) ^ N - (a : ℤ) ^ r) := by
  have ha' : Odd (a : ℤ) := by exact_mod_cast ha
  have h1 : IsCoprime (2 : ℤ) (-(a : ℤ) ^ r) :=
    ((odd_coprime_two _ ha').pow_left).symm.neg_right
  obtain ⟨s, rfl⟩ : ∃ s, N = s + 1 := ⟨N - 1, by omega⟩
  have e : (2 : ℤ) ^ (s + 1) - (a : ℤ) ^ r = -(a : ℤ) ^ r + 2 * 2 ^ s := by ring
  rw [e]; exact h1.add_mul_left_right _

theorem to_nat (x : ℕ) (y : ℤ) (h : IsCoprime (x : ℤ) y) : Nat.Coprime x y.natAbs := by
  have h' := Int.isCoprime_iff_gcd_eq_one.mp h
  rw [Int.gcd_eq_natAbs] at h'
  simpa using h'


theorem exp_eq (N r j : ℕ) (hcop : Nat.Coprime N r) (hr : 0 < r) (hj : j < r) :
    r * (N * j / r) + N * (r - 1 - j) = (N - 1) * (r - 1) + (r - 1 - N * j % r) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : r = 1 := by simpa using hcop
    subst h1
    have : j = 0 := by omega
    subst this
    simp
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h1 := Nat.div_add_mod ((M + 1) * j) r
    have h2 : (M + 1) * (r - 1 - j) + (M + 1) * j = (M + 1) * (r - 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    have h3 : (M + 1 - 1) * (r - 1) + (r - 1) = (M + 1) * (r - 1) := by
      rw [Nat.add_sub_cancel]; ring
    have h4 := Nat.mod_lt ((M + 1) * j) hr
    omega

theorem perm_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N r : ℕ) (hcop : Nat.Coprime N r)
    (hr : 0 < r) :
    ∑ j ∈ Finset.range r, f (N * j % r) = ∑ u ∈ Finset.range r, f u := by
  have hinj : Set.InjOn (fun j => N * j % r) ↑(Finset.range r) := by
    intro j1 hj1 j2 hj2 h
    simp only [Finset.coe_range, Set.mem_Iio] at hj1 hj2
    have h' : N * j1 ≡ N * j2 [MOD r] := h
    have h'' := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hcop) h'
    unfold Nat.ModEq at h''
    rwa [Nat.mod_eq_of_lt hj1, Nat.mod_eq_of_lt hj2] at h''
  have himg : (Finset.range r).image (fun j => N * j % r) = Finset.range r := by
    apply Finset.eq_of_subset_of_card_le
    · intro u hu
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_range.mpr (Nat.mod_lt _ hr)
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image (f := f) hinj, himg]


theorem root_exists : LaboK.kgeo_root_enonce := by
  intro a N r ha h1 h2 hcop
  set m := ((2 : ℤ) ^ N - (a : ℤ) ^ r).natAbs with hm
  have c2 : Nat.Coprime 2 m := to_nat 2 _ (by exact_mod_cast cop_two a N r ha (by omega))
  have ca : Nat.Coprime a m := to_nat a _ (cop_a a N r ha h1)
  have key : (2 : ZMod m) ^ N = (a : ZMod m) ^ r := by
    have h0 : (((2 : ℤ) ^ N - (a : ℤ) ^ r : ℤ) : ZMod m) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natAbs_dvd.mpr dvd_rfl)
    push_cast at h0
    exact sub_eq_zero.mp h0
  obtain ⟨U2, hU2⟩ : ∃ u : (ZMod m)ˣ, (u : ZMod m) = 2 :=
    ⟨ZMod.unitOfCoprime 2 c2, by simp [ZMod.coe_unitOfCoprime]⟩
  obtain ⟨Ua, hUa⟩ : ∃ u : (ZMod m)ˣ, (u : ZMod m) = a :=
    ⟨ZMod.unitOfCoprime a ca, by simp [ZMod.coe_unitOfCoprime]⟩
  have keyU : U2 ^ (N : ℤ) = Ua ^ (r : ℤ) := by
    ext
    simp only [zpow_natCast, Units.val_pow_eq_pow_val, hU2, hUa]
    exact key
  have bez : (N : ℤ) * N.gcdA r + (r : ℤ) * N.gcdB r = 1 := by
    have h := Nat.gcd_eq_gcd_ab N r
    rw [hcop.gcd_eq_one] at h
    push_cast at h
    linarith
  set A := N.gcdA r
  set B := N.gcdB r
  have er : (U2 ^ B * Ua ^ A) ^ (r : ℤ) = U2 := by
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm A (r : ℤ), zpow_mul Ua, ← keyU, ← zpow_mul,
      ← zpow_add, show B * (r : ℤ) + (N : ℤ) * A = 1 by linarith, zpow_one]
  have eN : (U2 ^ B * Ua ^ A) ^ (N : ℤ) = Ua := by
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm B (N : ℤ), zpow_mul U2, keyU, ← zpow_mul,
      ← zpow_add, show (r : ℤ) * B + A * (N : ℤ) = 1 by linarith, zpow_one]
  refine ⟨((U2 ^ B * Ua ^ A : (ZMod m)ˣ) : ZMod m), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, er, hU2]
  · rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, eN, hUa]

theorem ring_id : LaboK.kgeo_ring_enonce := by
  intro R _ a N r t hcop htr htN
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0; simp [LaboK.ChrisSum]
  have hterm : ∀ j ∈ Finset.range r, ((2 ^ (N * j / r) * a ^ (r - 1 - j) : ℕ) : R) =
      t ^ ((N - 1) * (r - 1)) * t ^ (r - 1 - N * j % r) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    push_cast
    rw [← htr, ← htN, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    exact exp_eq N r j hcop hr hj'
  unfold LaboK.ChrisSum
  rw [Nat.cast_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [perm_sum (fun u => t ^ (r - 1 - u)) N r hcop hr, Finset.sum_range_reflect]

end P2Kgeo

theorem kgeo_thm : LaboK.kgeo_enonce := by
  intro a N r ha h1 h2 hcop
  set m := ((2 : ℤ) ^ N - (a : ℤ) ^ r).natAbs with hm
  obtain ⟨t, htr, htN⟩ := P2Kgeo.root_exists a N r ha h1 h2 hcop
  have hring := P2Kgeo.ring_id (ZMod m) a N r t hcop htr htN
  have c2 : Nat.Coprime 2 m :=
    P2Kgeo.to_nat 2 _ (by exact_mod_cast P2Kgeo.cop_two a N r ha (by omega))
  have u2 : IsUnit (2 : ZMod m) := by
    have h := (ZMod.isUnit_iff_coprime 2 m).mpr c2
    simpa using h
  have ut : IsUnit t := (isUnit_pow_iff (n := r) (by omega)).mp (htr ▸ u2)
  have us : IsUnit (∑ s ∈ Finset.range r, t ^ s) :=
    IsUnit.of_mul_eq_one (t - 1) (by rw [geom_sum_mul, htr]; ring)
  have uC : IsUnit ((LaboK.ChrisSum a N r : ℕ) : ZMod m) := hring ▸ (ut.pow _).mul us
  have cop : Nat.Coprime (LaboK.ChrisSum a N r) m := (ZMod.isUnit_iff_coprime _ _).mp uC
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  simpa using cop
