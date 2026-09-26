import Labo.S4_Enonces

/-! S4-A · prouveur P2 · node k2NormalForm (L3, form). Self-contained: helpers in namespace P2NF
(phases toolkit, twoBlocks and phasesTransversal repeated from Tent_twoBlocks_P2 / Tent_phasesTransversal_P2).
Idea: twoBlocks gives [a, a+l) u [b, b+m); transversal gives card = r = l + m and injectivity mod r,
hence surjectivity onto Z/r; the phase y = a + l (mod r) lies neither in the first block (0 < a+l-y < r)
nor at b + j with j >= 1 (else y - 1 = a + l - 1 mod r, two phases); so b = a + l + g r, g >= 1. -/

namespace P2NF
open LaboF

lemma getD_ge (w : List Bool) {k : ℕ} (h : w.length ≤ k) : w.getD k false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma lt_of_getD (w : List Bool) {k : ℕ} (h : w.getD k false = true) : k < w.length := by
  by_contra hc
  rw [getD_ge w (by omega)] at h
  exact Bool.false_ne_true h

/-- number of ones strictly before position `i` -/
def F (w : List Bool) (i : ℕ) : ℕ := ((Finset.range i).filter (fun k => w.getD k false = true)).card

lemma F_zero (w : List Bool) : F w 0 = 0 := by simp [F]

lemma F_succ (w : List Bool) (k : ℕ) :
    F w (k + 1) = F w k + if w.getD k false = true then 1 else 0 := by
  unfold F
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

lemma take_count (w : List Bool) (i : ℕ) : (w.take i).count true = F w i := by
  induction i with
  | zero => simp [F]
  | succ i ih =>
    rw [List.take_add_one, List.count_append, ih, F_succ, List.getD_eq_getElem?_getD]
    rcases w[i]? with _ | b
    · simp
    · cases b <;> simp

lemma F_length (w : List Bool) : F w w.length = w.count true := by
  rw [← take_count, List.take_length]

lemma F_mono (w : List Bool) {i j : ℕ} (h : i ≤ j) : F w i ≤ F w j := by
  unfold F
  exact Finset.card_le_card (Finset.filter_subset_filter _ (by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega))

lemma F_const (w : List Bool) {a j : ℕ} (haj : a ≤ j) :
    (∀ k, a ≤ k → k < j → w.getD k false ≠ true) → F w j = F w a := by
  induction j, haj using Nat.le_induction with
  | base => intro _; rfl
  | succ j hj ih =>
    intro h
    rw [F_succ, ih (fun k h1 h2 => h k h1 (by omega)), if_neg (h j hj (by omega))]
    simp

/-- the phase of position `i` -/
def ph (w : List Bool) (i : ℕ) : ℤ := (w.count true : ℤ) * (i : ℤ) - (w.length : ℤ) * (F w i : ℤ)

def Pos (w : List Bool) : Finset ℕ := (Finset.range w.length).filter (fun i => w.getD i false = true)

lemma phases_eq (w : List Bool) : phases w = (Pos w).image (ph w) := by
  simp only [phases, Pos, take_count]
  rfl

lemma mem_phases {w : List Bool} {y : ℤ} :
    y ∈ phases w ↔ ∃ i, i < w.length ∧ w.getD i false = true ∧ ph w i = y := by
  rw [phases_eq]
  simp only [Pos, Finset.mem_image, Finset.mem_filter, Finset.mem_range, and_assoc]

lemma dvd_small {r x : ℤ} (h : r ∣ x) (h1 : -r < x) (h2 : x < r) : x = 0 := by
  obtain ⟨t, rfl⟩ := h
  rcases lt_trichotomy t 0 with ht | ht | ht
  · nlinarith
  · simp [ht]
  · nlinarith

/-- L2 : successor phase -/
lemma succ_loc : LaboF.phasesSucc_enonce := by
  classical
  intro w y hy
  rw [mem_phases] at hy
  obtain ⟨i, hiN, hi, rfl⟩ := hy
  by_cases hA : ∃ j, i < j ∧ w.getD j false = true
  · obtain ⟨hij, hj⟩ := Nat.find_spec hA
    have hjmin : ∀ k, i < k → k < Nat.find hA → w.getD k false ≠ true :=
      fun k h1 h2 hk => Nat.find_min hA h2 ⟨h1, hk⟩
    have hjN : Nat.find hA < w.length := lt_of_getD w hj
    have hFj : F w (Nat.find hA) = F w i + 1 := by
      rw [F_const w (a := i + 1) (by omega) (fun k h1 h2 => hjmin k (by omega) h2), F_succ, if_pos hi]
    refine ⟨ph w (Nat.find hA), mem_phases.2 ⟨_, hjN, hj, rfl⟩, ?_, ?_⟩
    · apply (Int.modEq_iff_dvd).2
      refine ⟨(i : ℤ) - (Nat.find hA : ℤ), ?_⟩
      unfold ph
      rw [hFj]
      push_cast
      ring
    · have key : (0 : ℤ) ≤ (w.count true : ℤ) * ((Nat.find hA : ℤ) - i - 1) :=
        mul_nonneg (by positivity) (by omega)
      unfold ph
      rw [hFj]
      push_cast
      nlinarith [key]
  · have hex : ∃ j, w.getD j false = true := ⟨i, hi⟩
    have hj := Nat.find_spec hex
    have hji : Nat.find hex ≤ i := Nat.find_min' hex hi
    have hF0 : F w (Nat.find hex) = 0 := by
      rw [F_const w (a := 0) (by omega) (fun k _ h2 => Nat.find_min hex h2), F_zero]
    have hFN : w.count true = F w i + 1 := by
      rw [← F_length, F_const w (a := i + 1) (by omega)
        (fun k h1 _ hk => hA ⟨k, by omega, hk⟩), F_succ, if_pos hi]
    have hjN : Nat.find hex < w.length := lt_of_getD w hj
    refine ⟨ph w (Nat.find hex), mem_phases.2 ⟨_, hjN, hj, rfl⟩, ?_, ?_⟩
    · apply (Int.modEq_iff_dvd).2
      refine ⟨(i : ℤ) - (w.length : ℤ) - (Nat.find hex : ℤ), ?_⟩
      unfold ph
      rw [hF0, hFN]
      push_cast
      ring
    · have key : (0 : ℤ) ≤ (w.count true : ℤ) * ((w.length : ℤ) - 1 - i + (Nat.find hex : ℤ)) :=
        mul_nonneg (by positivity) (by omega)
      unfold ph
      rw [hF0]
      have hFN' : (w.count true : ℤ) = (F w i : ℤ) + 1 := by exact_mod_cast hFN
      push_cast
      rw [hFN'] at key ⊢
      nlinarith [key]

/-- transversal -/
lemma trans_loc : LaboF.phasesTransversal_enonce := by
  intro w hcop
  have main : ∀ i j, i < j → j < w.length → w.getD i false = true → w.getD j false = true →
      ¬ (ph w i ≡ ph w j [ZMOD (w.count true : ℤ)]) := by
    intro i j hij hjN hi hj hmod
    have h1 : F w i + 1 ≤ F w j := by
      have h := F_mono w (show i + 1 ≤ j by omega)
      rwa [F_succ, if_pos hi] at h
    have h2 : F w j + 1 ≤ w.count true := by
      have h := F_mono w (show j + 1 ≤ w.length by omega)
      rwa [F_succ, if_pos hj, F_length] at h
    have hd : (w.count true : ℤ) ∣ (w.length : ℤ) * ((F w j : ℤ) - F w i) := by
      have h := (Int.modEq_iff_dvd).1 hmod
      have e : (w.length : ℤ) * ((F w j : ℤ) - F w i) =
          (w.count true : ℤ) * ((j : ℤ) - i) - (ph w j - ph w i) := by
        unfold ph; ring
      rw [e]
      exact dvd_sub (dvd_mul_right _ _) h
    have hc : IsCoprime (w.count true : ℤ) (w.length : ℤ) := (Nat.isCoprime_iff_coprime.2 hcop).symm
    have h3 := dvd_small (hc.dvd_of_dvd_mul_left hd) (by omega) (by omega)
    omega
  have key : ∀ i j, i < w.length → w.getD i false = true → j < w.length → w.getD j false = true →
      ph w i ≡ ph w j [ZMOD (w.count true : ℤ)] → i = j := by
    intro i j hi hwi hj hwj hmod
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hmod (main i j h hj hwi hwj)
    · exact h
    · exact absurd hmod.symm (main j i h hi hwj hwi)
  constructor
  · rw [phases_eq, Finset.card_image_of_injOn, ← F_length]
    · rfl
    · intro i hi j hj hij
      simp only [Pos, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
      exact key i j hi.1 hi.2 hj.1 hj.2 (hij ▸ Int.ModEq.refl _)
  · intro y hy z hz hyz
    obtain ⟨i, hi, hwi, rfl⟩ := mem_phases.1 hy
    obtain ⟨j, hj, hwj, rfl⟩ := mem_phases.1 hz
    rw [key i j hi hwi hj hwj hyz]

end P2NF
namespace P2NF
open LaboF

lemma exists_up (S : Finset ℤ) (a : ℤ) : ∃ k : ℕ, a + (k : ℤ) ∉ S := by
  by_contra h
  push_neg at h
  have hinf : (S : Set ℤ).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => a + (k : ℤ))
      (fun i j hij => by simp only at hij; omega) h
  exact hinf S.finite_toSet

lemma exists_down (S : Finset ℤ) (x : ℤ) : ∃ n : ℕ, x - (n : ℤ) - 1 ∉ S := by
  by_contra h
  push_neg at h
  have hinf : (S : Set ℤ).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => x - (k : ℤ) - 1)
      (fun i j hij => by simp only at hij; omega) h
  exact hinf S.finite_toSet


lemma two_loc : LaboF.twoBlocks_enonce := by
  classical
  intro S hS
  unfold blocks at hS
  obtain ⟨p, q, hpq, hPQ⟩ := Finset.card_eq_two.mp hS
  have hstart : ∀ x, x ∈ S → x - 1 ∉ S → x = p ∨ x = q := by
    intro x hx hx1
    have hmem : x ∈ S.filter (fun x => x - 1 ∉ S) := Finset.mem_filter.mpr ⟨hx, hx1⟩
    rw [hPQ] at hmem
    simpa using hmem
  have hp : p ∈ S ∧ p - 1 ∉ S := by
    have hmem : p ∈ S.filter (fun x => x - 1 ∉ S) := by rw [hPQ]; simp
    exact Finset.mem_filter.mp hmem
  have hq : q ∈ S ∧ q - 1 ∉ S := by
    have hmem : q ∈ S.filter (fun x => x - 1 ∉ S) := by rw [hPQ]; simp
    exact Finset.mem_filter.mp hmem
  obtain ⟨a, b, hab, ha, hb, hst⟩ : ∃ a b : ℤ, a < b ∧ (a ∈ S ∧ a - 1 ∉ S) ∧ (b ∈ S ∧ b - 1 ∉ S) ∧
      ∀ x, x ∈ S → x - 1 ∉ S → x = a ∨ x = b := by
    rcases lt_or_gt_of_ne hpq with h | h
    · exact ⟨p, q, h, hp, hq, hstart⟩
    · exact ⟨q, p, h, hq, hp, fun x h1 h2 => (hstart x h1 h2).symm⟩
  set l := Nat.find (exists_up S a) with hldef
  have hl : a + (l : ℤ) ∉ S := Nat.find_spec (exists_up S a)
  have hl' : ∀ k < l, a + (k : ℤ) ∈ S := fun k hk => not_not.mp (Nat.find_min (exists_up S a) hk)
  set m := Nat.find (exists_up S b) with hmdef
  have hm : b + (m : ℤ) ∉ S := Nat.find_spec (exists_up S b)
  have hm' : ∀ k < m, b + (k : ℤ) ∈ S := fun k hk => not_not.mp (Nat.find_min (exists_up S b) hk)
  have l1 : 1 ≤ l := by
    by_contra h0
    have h00 : l = 0 := by omega
    apply hl
    rw [h00]
    simpa using ha.1
  have m1 : 1 ≤ m := by
    by_contra h0
    have h00 : m = 0 := by omega
    apply hm
    rw [h00]
    simpa using hb.1
  have hbl : a + (l : ℤ) < b := by
    by_contra hc
    push_neg at hc
    apply hb.2
    have hk : (b - 1 - a).toNat < l := by omega
    have h2 := hl' _ hk
    rwa [show a + ((b - 1 - a).toNat : ℤ) = b - 1 by omega] at h2
  have main : ∀ n : ℕ, ∀ x, x ∈ S → x - (n : ℤ) - 1 ∉ S →
      (a ≤ x ∧ x < a + (l : ℤ)) ∨ (b ≤ x ∧ x < b + (m : ℤ)) := by
    intro n
    induction n with
    | zero =>
      intro x hx hx1
      simp only [Nat.cast_zero, sub_zero] at hx1
      rcases hst x hx hx1 with rfl | rfl <;> omega
    | succ n ih =>
      intro x hx hxn
      by_cases h1 : x - 1 ∈ S
      · have h2 : x - 1 - (n : ℤ) - 1 ∉ S := by
          rwa [show x - 1 - (n : ℤ) - 1 = x - ((n + 1 : ℕ) : ℤ) - 1 by push_cast; ring]
        rcases ih (x - 1) h1 h2 with h | h
        · left
          refine ⟨by omega, ?_⟩
          by_contra hc
          have hx' : x = a + (l : ℤ) := by omega
          exact hl (hx' ▸ hx)
        · right
          refine ⟨by omega, ?_⟩
          by_contra hc
          have hx' : x = b + (m : ℤ) := by omega
          exact hm (hx' ▸ hx)
      · rcases hst x hx h1 with rfl | rfl <;> omega
  refine ⟨a, b, l, m, l1, m1, hbl, ?_⟩
  ext x
  simp only [Finset.mem_union, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_down S x
    exact main n x hx hn
  · rintro (h | h)
    · have h2 := hl' (x - a).toNat (by omega)
      rwa [show a + ((x - a).toNat : ℤ) = x by omega] at h2
    · have h2 := hm' (x - b).toNat (by omega)
      rwa [show b + ((x - b).toNat : ℤ) = x by omega] at h2

end P2NF
namespace P2NF
open LaboF

/-- L3 normal form -/
lemma nf_loc : LaboF.k2NormalForm_enonce := by
  intro w hcop hbl
  obtain ⟨a, b, l, m, hl, hm, hab, hS⟩ := two_loc _ hbl
  obtain ⟨hcard, hinj⟩ := trans_loc w hcop
  have hlm : l + m = w.count true := by
    rw [← hcard, hS, Finset.card_union_of_disjoint, Int.card_Ico, Int.card_Ico]
    · omega
    · rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [Finset.mem_Ico] at h1 h2
      omega
  have hr0 : 0 < w.count true := by omega
  have hsurj : ∀ t : ℤ, ∃ y ∈ phases w, y % (w.count true : ℤ) = t % (w.count true : ℤ) := by
    intro t
    have hsub : (phases w).image (fun y => y % (w.count true : ℤ)) ⊆ Finset.Ico 0 (w.count true : ℤ) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, -, rfl⟩ := hx
      rw [Finset.mem_Ico]
      exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
    have hcardim : ((phases w).image (fun y => y % (w.count true : ℤ))).card = w.count true := by
      rw [Finset.card_image_of_injOn, hcard]
      intro y hy z hz hyz
      exact hinj y hy z hz hyz
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Int.card_Ico, hcardim]; omega)
    have ht : t % (w.count true : ℤ) ∈ Finset.Ico 0 (w.count true : ℤ) := by
      rw [Finset.mem_Ico]
      exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
    rw [← heq, Finset.mem_image] at ht
    exact ht
  obtain ⟨y, hy, hyr⟩ := hsurj (a + l)
  have hyr' : y ≡ a + l [ZMOD (w.count true : ℤ)] := hyr
  have hyS := hy
  rw [hS, Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico] at hyS
  have hyb : y = b := by
    rcases hyS with h | h
    · exfalso
      have h0 := dvd_small (Int.ModEq.dvd hyr') (by omega) (by omega)
      omega
    · by_contra hne
      have h1 : y - 1 ∈ phases w := by
        rw [hS]; simp only [Finset.mem_union, Finset.mem_Ico]; omega
      have h2 : a + l - 1 ∈ phases w := by
        rw [hS]; simp only [Finset.mem_union, Finset.mem_Ico]; omega
      have h3 := hinj _ h1 _ h2 (Int.ModEq.sub_right 1 hyr')
      omega
  subst hyb
  obtain ⟨t, ht⟩ := Int.ModEq.dvd hyr'.symm
  have hr0' : (0 : ℤ) < w.count true := by exact_mod_cast hr0
  have ht1 : 1 ≤ t := by
    by_contra h
    push_neg at h
    nlinarith
  refine ⟨a, t.toNat, l, by omega, hl, by omega, ?_⟩
  have hG : ((t.toNat : ℕ) : ℤ) * (w.count true : ℤ) = y - a - l := by
    rw [Int.toNat_of_nonneg (by omega)]
    linarith
  have hr : (w.count true : ℤ) = l + m := by exact_mod_cast hlm.symm
  rw [hS]
  ext x
  simp only [Phi2, Finset.mem_image, Finset.mem_union, Finset.mem_Ico]
  rw [hG]
  constructor
  · rintro (h | h)
    · exact ⟨x - a, Or.inl ⟨by omega, by omega⟩, by ring⟩
    · exact ⟨x - a, Or.inr ⟨by omega, by omega⟩, by ring⟩
  · rintro ⟨u, hu, rfl⟩
    omega

end P2NF


theorem k2NormalForm_thm : LaboF.k2NormalForm_enonce := P2NF.nf_loc
