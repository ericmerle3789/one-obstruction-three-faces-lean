import Labo.S4_Enonces

/-! S4-A · prouveur P2 · node k2ValidBound (L3, validity bound). Self-contained: helpers in
namespace P2VB (phases toolkit + L2 successor, repeated from Tent_phasesSucc_P2).
Idea: N = q r + rho, 1 <= rho < r (gcd = 1); c = max(lam, rho); the phase y = s + c + g r (2nd block)
has its L2 successor z of residue c - rho in [0, lam): z = s + c - rho (unique in Phi2);
y - z = g r + rho <= N - r gives g <= q - 1. -/

namespace P2VB
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

end P2VB
namespace P2VB
open LaboF

/-- L3 validity bound -/
lemma vb_loc : LaboF.k2ValidBound_enonce := by
  intro w s g lam hcop hg hlam hlr hph
  have hr0 : 0 < w.count true := by omega
  have hNqr : w.length = w.count true * (w.length / w.count true) + w.length % w.count true :=
    (Nat.div_add_mod _ _).symm
  have hρr : w.length % w.count true < w.count true := Nat.mod_lt _ hr0
  have hρ0 : 0 < w.length % w.count true := by
    by_contra h0
    have hdvd : w.count true ∣ w.length := Nat.dvd_of_mod_eq_zero (by omega)
    have h1 : Nat.gcd (w.count true) w.length = 1 := hcop.symm
    rw [Nat.gcd_eq_left hdvd] at h1
    omega
  generalize w.length / w.count true = q at hNqr ⊢
  generalize w.length % w.count true = ρ at hNqr hρr hρ0
  have hN : (w.length : ℤ) = (w.count true : ℤ) * (q : ℤ) + (ρ : ℤ) := by exact_mod_cast hNqr
  have hc1 : lam ≤ max lam ρ := le_max_left _ _
  have hc2 : ρ ≤ max lam ρ := le_max_right _ _
  have hc3 : max lam ρ < w.count true := max_lt hlr hρr
  have hc4 : max lam ρ < lam + ρ := by omega
  generalize max lam ρ = c at hc1 hc2 hc3 hc4
  have hy : (c : ℤ) + (g : ℤ) * (w.count true : ℤ) + s ∈ phases w := by
    rw [hph, Finset.mem_image]
    refine ⟨(c : ℤ) + (g : ℤ) * (w.count true : ℤ), ?_, rfl⟩
    simp only [Phi2, Finset.mem_union, Finset.mem_Ico]
    right
    have e1 : (lam : ℤ) ≤ c := by exact_mod_cast hc1
    have e2 : (c : ℤ) < w.count true := by exact_mod_cast hc3
    constructor <;> linarith
  obtain ⟨z, hz, hzmod, hzle⟩ := succ_loc w _ hy
  rw [hph, Finset.mem_image] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  simp only [Phi2, Finset.mem_union, Finset.mem_Ico] at hu
  have hd := (Int.modEq_iff_dvd).1 hzmod
  have hd2 : (w.count true : ℤ) ∣ (c : ℤ) - ρ - u := by
    have e : (c : ℤ) - ρ - u = ((c : ℤ) + (g : ℤ) * (w.count true : ℤ) + s - (w.length : ℤ) - (u + s))
        - (w.count true : ℤ) * ((g : ℤ) - q) := by rw [hN]; ring
    rw [e]
    exact dvd_sub hd (dvd_mul_right _ _)
  rcases hu with hu | hu
  · have h0 := dvd_small hd2 (by omega) (by omega)
    have hgr : (g : ℤ) * (w.count true : ℤ) ≤ (w.count true : ℤ) * (q : ℤ) - (w.count true : ℤ) := by
      rw [hN] at hzle; linarith
    by_contra hcon
    push_neg at hcon
    have hqg : (q : ℤ) ≤ (g : ℤ) := by exact_mod_cast (Nat.lt_succ_iff.mp hcon)
    have hr0' : (0 : ℤ) < w.count true := by exact_mod_cast hr0
    nlinarith
  · exfalso
    have hd3 : (w.count true : ℤ) ∣ (c : ℤ) - ρ - (u - (g : ℤ) * (w.count true : ℤ)) := by
      have e : (c : ℤ) - ρ - (u - (g : ℤ) * (w.count true : ℤ)) =
          ((c : ℤ) - ρ - u) + (w.count true : ℤ) * g := by ring
      rw [e]
      exact dvd_add hd2 (dvd_mul_right _ _)
    have e1 : (c : ℤ) < lam + ρ := by exact_mod_cast hc4
    have e2 : (ρ : ℤ) ≤ c := by exact_mod_cast hc2
    have h0 := dvd_small hd3 (by linarith) (by linarith)
    linarith

end P2VB


theorem k2ValidBound_thm : LaboF.k2ValidBound_enonce := P2VB.vb_loc
