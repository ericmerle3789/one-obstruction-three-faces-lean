import Mathlib
import Labo.HH1997_Enonces
import OneObstruction.TransportRecurrence

/-!
# LABO-COLLATZ · HH1997 · formaliste (2026-10-19) — PROOFS of `Labo/HH1997_Enonces.lean`

Halbeisen–Hungerbühler 1997, Acta Arith. 78: (2), (3), (4), Lemma 2, Lemma 4, Lemma 5, Corollary 1, (13), Lemma 9.
Every proof is complete and kernel-checked; axiom log: `Labo/HH1997_Axiomes.lean`.

Reused, with credit:
* `LaboBP.C_eq_Csum` (`Labo/S2_Pont.lean`) gives (3) once `phi = LaboBP.C` (`phi_eq_C_thm`);
* `LaboBP.d_ne_zero` (`Labo/S2_Pont.lean`) gives `2^l ≠ 3^n` in Lemma 2;
* `ContentDescent.W0_append` (kernel) gives (4) on block words (`eq4_kernel_thm`), through the bridge
  `W0 = (2^K − 3^n) + ϕ` (`W0_bridge_thm`, new);
* `CollatzTransport.collapse_of_recurrence`, `coprime_pow_two`, `coprime_pow_three` (kernel) give the core of
  Lemma 9 (`core_dvd`): along the right shift ρ, (13) is a transport chain `U·R(r+1) = 2·R(r) + C·q`.
Proof routes that differ from the paper: Lemma 4 goes through the Abel identity
`2ϕ(s) + 2^l = 3^n + Σ_{j<l} 3^{#1 after j+1} 2^j` (each prefix sum enters with a decreasing weight) instead of
the paper's sequence of swaps; (15) is proved for every divisor of `2^l − 3^n` (the paper's last line is a sketch).
-/

namespace LaboHH

open LaboBP

/-! ## (2), (4), (3) and the bridges -/

@[simp] lemma phi_nil : phi [] = 0 := rfl

lemma phi_append_false (s : List Bool) : phi (s ++ [false]) = phi s := by
  simp [phi, phiRev]

lemma phi_append_true (s : List Bool) : phi (s ++ [true]) = 3 * phi s + 2 ^ s.length := by
  simp [phi, phiRev]

theorem eq2_thm : eq2 := ⟨rfl, fun s => ⟨phi_append_false s, phi_append_true s⟩⟩

theorem eq4_thm : eq4 := by
  intro s t
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t b ih =>
    rw [← List.append_assoc]
    cases b
    · rw [phi_append_false, phi_append_false, ih]
      simp [List.count_append]
    · rw [phi_append_true, phi_append_true, ih]
      simp only [List.count_append, List.length_append, List.count_singleton_self, pow_add, pow_one]
      ring

lemma phi_cons (b : Bool) (w : List Bool) :
    phi (b :: w) = (if b then 3 ^ w.count true else 0) + 2 * phi w := by
  have h := eq4_thm [b] w
  rw [List.singleton_append] at h
  rw [h]
  cases b <;> simp [phi, phiRev]

theorem phi_eq_C_thm : phi_eq_C := by
  intro s
  induction s with
  | nil => rfl
  | cons b w ih => rw [phi_cons, ih]; rfl

theorem eq3_thm : eq3 := by
  intro s
  rw [phi_eq_C_thm s, C_eq_Csum s]
  unfold Csum
  refine Finset.sum_congr rfl fun j _ => ?_
  cases s.getD j false <;> simp [mul_comm]

lemma encode_cons (m s : ℕ) (l : List (ℕ × ℕ)) :
    encode ((m, s) :: l) = List.replicate m true ++ List.replicate s false ++ encode l := by
  simp [encode]

lemma encode_append (l₁ l₂ : List (ℕ × ℕ)) : encode (l₁ ++ l₂) = encode l₁ ++ encode l₂ := by
  simp [encode]

lemma encode_length (l : List (ℕ × ℕ)) : (encode l).length = ContentDescent.mssum l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨m, s⟩ := p
    rw [encode_cons, ContentDescent.mssum_cons]
    simp only [List.length_append, List.length_replicate, ih]

lemma encode_count (l : List (ℕ × ℕ)) : (encode l).count true = ContentDescent.msum l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨m, s⟩ := p
    rw [encode_cons, ContentDescent.msum_cons]
    simp [List.count_replicate, ih]

lemma phi_rep_true (m : ℕ) : (phi (List.replicate m true) : ℤ) = 3 ^ m - 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', phi_append_true, List.length_replicate]
    push_cast
    rw [ih]
    ring

lemma phi_append_rep_false (u : List Bool) (s : ℕ) : phi (u ++ List.replicate s false) = phi u := by
  induction s with
  | zero => simp
  | succ s ih => rw [List.replicate_succ', ← List.append_assoc, phi_append_false, ih]

theorem W0_bridge_thm : W0_bridge := by
  intro l
  refine ⟨encode_length l, encode_count l, ?_⟩
  induction l with
  | nil => simp [LaboBP.d, encode]
  | cons p l ih =>
    obtain ⟨m, s⟩ := p
    simp only [LaboBP.d, encode_length, encode_count] at ih ⊢
    rw [ContentDescent.W0_cons, ih, encode_cons, eq4_thm, phi_append_rep_false,
      ContentDescent.mssum_cons, ContentDescent.msum_cons]
    push_cast
    rw [phi_rep_true]
    simp only [List.length_append, List.length_replicate, encode_count]
    ring

/-- (4) on block words from the kernel cocycle `ContentDescent.W0_append` and the bridge. -/
theorem eq4_kernel_thm : eq4_kernel := by
  intro l₁ l₂
  have hA := ContentDescent.W0_append l₁ l₂
  have h12 := (W0_bridge_thm (l₁ ++ l₂)).2.2
  have h1 := (W0_bridge_thm l₁).2.2
  have h2 := (W0_bridge_thm l₂).2.2
  rw [encode_append] at h12
  simp only [LaboBP.d, List.length_append, List.count_append, encode_length, encode_count] at h12 h1 h2
  rw [h12, h1, h2] at hA
  rw [encode_count, encode_length]
  have : ((phi (encode l₁ ++ encode l₂) : ℕ) : ℤ)
      = 3 ^ ContentDescent.msum l₂ * phi (encode l₁) + 2 ^ ContentDescent.mssum l₁ * phi (encode l₂) := by
    linear_combination hA
  exact_mod_cast this

/-! ## Lemma 2 -/

lemma phiMap_nil {K : Type*} [Field K] (x : K) : phiMap [] x = x := rfl

lemma phiMap_append_singleton {K : Type*} [Field K] (s : List Bool) (b : Bool) (x : K) :
    phiMap (s ++ [b]) x = gStep b (phiMap s x) := by
  simp [phiMap, List.foldl_append]

theorem lemma2_affine_thm : lemma2_affine := by
  intro K _ _ s x
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  induction s using List.reverseRecOn with
  | nil => simp [phiMap_nil]
  | append_singleton s b ih =>
    rw [phiMap_append_singleton, ih]
    cases b
    · rw [phi_append_false]
      simp only [gStep, Bool.false_eq_true, ↓reduceIte, List.count_append, List.length_append,
        List.length_singleton, pow_succ]
      simp only [List.count_singleton, beq_iff_eq]
      field_simp
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring
    · rw [phi_append_true]
      simp only [gStep, ↓reduceIte, List.count_append, List.count_singleton_self, List.length_append,
        List.length_singleton, pow_succ]
      push_cast
      field_simp
      ring

theorem lemma2_fixed_thm : lemma2_fixed := by
  intro K _ _ s hs
  have hD : (2 : K) ^ s.length - 3 ^ s.count true ≠ 0 := by
    have h := d_ne_zero s hs
    have hc : ((d s : ℤ) : K) = (2 : K) ^ s.length - 3 ^ s.count true := by simp [LaboBP.d]
    rw [← hc]
    exact_mod_cast h
  refine ⟨hD, fun x => ?_⟩
  rw [lemma2_affine_thm K s x]
  have h2 : (2 : K) ^ s.length ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [div_eq_iff h2, eq_div_iff hD]
  constructor <;> intro h <;> linear_combination -h

/-- `3^{n(p)}·ϕ(s) + 2^l·ϕ(p) = 2^i·ϕ(λ^i s) + 3^n·ϕ(p)` for the prefix `p = s₁…s_i`. -/
lemma rot_key (s : List Bool) (i : ℕ) (hi : i ≤ s.length) :
    3 ^ (s.take i).count true * phi s + 2 ^ s.length * phi (s.take i)
      = 2 ^ i * phi (s.rotate i) + 3 ^ s.count true * phi (s.take i) := by
  have hs : s = s.take i ++ s.drop i := (List.take_append_drop i s).symm
  have hlen : (s.take i).length = i := by rw [List.length_take, Nat.min_eq_left hi]
  have hrot : s.rotate i = s.drop i ++ s.take i := List.rotate_eq_drop_append_take hi
  have hphi : phi s = 3 ^ (s.drop i).count true * phi (s.take i) + 2 ^ i * phi (s.drop i) := by
    conv_lhs => rw [hs]
    rw [eq4_thm, hlen]
  have hc : s.count true = (s.take i).count true + (s.drop i).count true := by
    conv_lhs => rw [hs]
    rw [List.count_append]
  have hl : s.length = i + (s.drop i).length := by rw [List.length_drop]; omega
  rw [hrot, eq4_thm, hphi, hc, hl, pow_add, pow_add]
  ring

lemma orbit_formula (s : List Bool) (hs : s ≠ []) (i : ℕ) (hi : i ≤ s.length) :
    phiMap (s.take i) ((phi s : ℚ) / (d s : ℚ)) = (phi (s.rotate i) : ℚ) / (d s : ℚ) := by
  have hD : (d s : ℚ) ≠ 0 := by exact_mod_cast d_ne_zero s hs
  have hdq : (d s : ℚ) = 2 ^ s.length - 3 ^ s.count true := by simp [LaboBP.d]
  have hlen : (s.take i).length = i := by rw [List.length_take, Nat.min_eq_left hi]
  rw [lemma2_affine_thm ℚ, hlen]
  have key : (3 : ℚ) ^ (s.take i).count true * phi s + 2 ^ s.length * phi (s.take i)
      = 2 ^ i * phi (s.rotate i) + 3 ^ s.count true * phi (s.take i) := by
    exact_mod_cast rot_key s i hi
  rw [div_eq_div_iff (by positivity) hD]
  have hexp : (3 ^ (s.take i).count true * ((phi s : ℚ) / (d s : ℚ)) + phi (s.take i)) * (d s : ℚ)
      = 3 ^ (s.take i).count true * phi s + phi (s.take i) * (d s : ℚ) := by
    field_simp
  rw [hexp, hdq]
  linear_combination key

/-- A rational `a / D` with `D` odd: odd denominator, and the reduced numerator has the parity of `a`. -/
lemma num_parity (a D : ℤ) (hD : Odd D) :
    ((((a : ℚ) / D).num % 2 = 0) ↔ a % 2 = 0) ∧ Odd (((a : ℚ) / D).den) := by
  have hD0 : D ≠ 0 := by rintro rfl; simp at hD
  have hden : ((((a : ℚ) / D).den : ℕ) : ℤ) ∣ D := by
    have := Rat.den_dvd a D
    rwa [Rat.divInt_eq_div] at this
  have hodd : Odd (((a : ℚ) / D).den) :=
    Odd.of_dvd_nat (Int.natAbs_odd.mpr hD) (Int.ofNat_dvd_left.mp hden)
  refine ⟨?_, hodd⟩
  have hcross : ((a : ℚ) / D).num * D = a * ((a : ℚ) / D).den := by
    have h1 : ((((a : ℚ) / D).num : ℤ) : ℚ) / ((((a : ℚ) / D).den : ℕ) : ℚ) = (a : ℚ) / D :=
      Rat.num_div_den _
    have hden0 : ((((a : ℚ) / D).den : ℕ) : ℚ) ≠ 0 := by positivity
    have hD0' : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
    rw [div_eq_div_iff hden0 hD0'] at h1
    exact_mod_cast h1
  have hDn : ¬ Even D := Int.not_even_iff_odd.mpr hD
  have hdn : ¬ Even ((((a : ℚ) / D).den : ℕ) : ℤ) := by
    rw [Int.not_even_iff_odd]
    exact_mod_cast hodd
  rw [← Int.even_iff, ← Int.even_iff]
  constructor
  · intro he
    have h2 : Even (a * ((a : ℚ) / D).den) := hcross ▸ he.mul_right D
    rcases Int.even_mul.mp h2 with h | h
    · exact h
    · exact absurd h hdn
  · intro he
    have h2 : Even (((a : ℚ) / D).num * D) := hcross ▸ he.mul_right _
    rcases Int.even_mul.mp h2 with h | h
    · exact h
    · exact absurd h hDn

lemma phi_rot_parity (s : List Bool) (i : ℕ) (hi : i < s.length) :
    ((phi (s.rotate i) : ℤ) % 2 = 0 ↔ s[i] = false) := by
  have hrot : s.rotate i = s[i] :: (s.drop (i + 1) ++ s.take i) := by
    rw [List.rotate_eq_drop_append_take hi.le, List.drop_eq_getElem_cons hi, List.cons_append]
  rw [hrot, phi_cons]
  have h3 : ∀ c : ℕ, 3 ^ c % 2 = 1 := fun c => by rw [Nat.pow_mod]; simp
  have h4 := h3 ((s.drop (i + 1) ++ s.take i).count true)
  generalize s[i] = b
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add, iff_true]
    omega
  · simp only [↓reduceIte, Bool.true_eq_false, iff_false]
    omega

lemma collatzQ_eq (y : ℚ) (a D : ℤ) (hD : Odd D) (hy : y = (a : ℚ) / D) (b : Bool)
    (hb : a % 2 = 0 ↔ b = false) : collatzQ y = gStep b y := by
  have hpar := (num_parity a D hD).1
  rw [← hy] at hpar
  unfold collatzQ gStep
  by_cases h : y.num % 2 = 0
  · have hb' : b = false := hb.mp (hpar.mp h)
    simp [h, hb']
  · have hb' : b = true := by
      cases b
      · exact absurd (hpar.mpr (hb.mpr rfl)) h
      · rfl
    simp [h, hb']

theorem lemma2_cycle_thm : lemma2_cycle := by
  intro s hs
  have hl : s.length ≠ 0 := by
    intro h
    exact hs (List.length_eq_zero_iff.mp h)
  have hDodd : Odd (d s) := by
    unfold LaboBP.d
    exact Even.sub_odd (even_two.pow_of_ne_zero hl) (Odd.pow (by decide))
  have horb : ∀ i, i ≤ s.length →
      collatzQ^[i] ((phi s : ℚ) / (d s : ℚ)) = phiMap (s.take i) ((phi s : ℚ) / (d s : ℚ)) := by
    intro i
    induction i with
    | zero => intro _; simp [phiMap_nil]
    | succ i ih =>
      intro hi
      rw [Function.iterate_succ_apply', ih (by omega), List.take_succ_eq_append_getElem (by omega),
        phiMap_append_singleton]
      apply collatzQ_eq _ (phi (s.rotate i)) (d s) hDodd
      · rw [orbit_formula s hs i (by omega)]
        simp
      · exact phi_rot_parity s i (by omega)
  refine ⟨hDodd, ?_, fun i hi => ⟨horb i hi, ?_⟩, ?_⟩
  · have := (num_parity (phi s) (d s) hDodd).2
    simpa using this
  · rw [horb i hi, orbit_formula s hs i hi]
    have := (num_parity (phi (s.rotate i)) (d s) hDodd).2
    simpa using this
  · rw [horb _ le_rfl, orbit_formula s hs _ le_rfl, List.rotate_length]

/-! ## Lemma 4 -/

lemma count_take_add_drop (s : List Bool) (k : ℕ) :
    (s.take k).count true + (s.drop k).count true = s.count true := by
  rw [← List.count_append, List.take_append_drop]

/-- Abel identity: `2ϕ(s) + 2^l = 3^n + Σ_{j<l} 3^{#1 in s_{j+2}…s_l} 2^j`. -/
lemma abel (s : List Bool) :
    2 * phi s + 2 ^ s.length
      = 3 ^ s.count true + ∑ j ∈ Finset.range s.length, 3 ^ ((s.drop (j + 1)).count true) * 2 ^ j := by
  induction s with
  | nil => simp
  | cons b w ih =>
    rw [phi_cons, List.length_cons, Finset.sum_range_succ']
    simp only [List.drop_succ_cons, List.drop_zero, pow_zero, mul_one]
    have hsum : ∑ j ∈ Finset.range w.length, 3 ^ ((w.drop (j + 1)).count true) * 2 ^ (j + 1)
        = 2 * ∑ j ∈ Finset.range w.length, 3 ^ ((w.drop (j + 1)).count true) * 2 ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum, pow_succ]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, List.count_cons, beq_iff_eq, add_zero]
      omega
    · simp only [↓reduceIte, List.count_cons_self, pow_succ]
      omega

lemma prefix_count_ext : ∀ s t : List Bool, s.length = t.length →
    (∀ k, (s.take k).count true = (t.take k).count true) → s = t
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: s, b :: t, hl, h => by
    have hab : a = b := by
      have h1 := h 1
      cases a <;> cases b <;> simp_all
    subst hab
    congr 1
    apply prefix_count_ext s t (by simpa using hl)
    intro k
    have h2 := h (k + 1)
    simpa [List.take_succ_cons, List.count_cons] using h2

theorem lemma4_thm : lemma4 := by
  intro s t hl hn hne hdom
  have hab := abel s
  have hbt := abel t
  rw [← hl, ← hn] at hbt
  have hdrop : ∀ j, j < s.length → (t.drop (j + 1)).count true ≤ (s.drop (j + 1)).count true := by
    intro j hj
    have h1 := count_take_add_drop s (j + 1)
    have h2 := count_take_add_drop t (j + 1)
    have h3 := hdom (j + 1) (by omega) (by omega)
    omega
  have hle : ∀ j ∈ Finset.range s.length,
      3 ^ ((t.drop (j + 1)).count true) * 2 ^ j ≤ 3 ^ ((s.drop (j + 1)).count true) * 2 ^ j := by
    intro j hj
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (hdrop j (Finset.mem_range.mp hj)))
  have hlt : ∑ j ∈ Finset.range s.length, 3 ^ ((t.drop (j + 1)).count true) * 2 ^ j
      < ∑ j ∈ Finset.range s.length, 3 ^ ((s.drop (j + 1)).count true) * 2 ^ j := by
    apply Finset.sum_lt_sum hle
    by_contra hcon
    push Not at hcon
    apply hne
    apply prefix_count_ext s t hl
    intro k
    by_cases hk0 : k = 0
    · subst hk0; simp
    by_cases hkl : k ≤ s.length
    · have hj : k - 1 < s.length := by omega
      have heq := le_antisymm (hle _ (Finset.mem_range.mpr hj)) (hcon _ (Finset.mem_range.mpr hj))
      have h3 : 3 ^ ((t.drop (k - 1 + 1)).count true) = 3 ^ ((s.drop (k - 1 + 1)).count true) :=
        Nat.eq_of_mul_eq_mul_right (by positivity) heq
      have h4 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
      rw [show k - 1 + 1 = k by omega] at h4
      have h5 := count_take_add_drop s k
      have h6 := count_take_add_drop t k
      omega
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      exact hn
  omega

/-! ## Lemma 5 and Corollary 1 -/

lemma cl_le_iff {l n j k : ℕ} (hl : 0 < l) : cl l n j ≤ k ↔ j * n ≤ k * l := by
  unfold cl
  rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hl)]
  norm_cast

lemma cl_zero (l n : ℕ) : cl l n 0 = 0 := by simp [cl]

lemma cl_add_le (l n a b : ℕ) : cl l n (a + b) ≤ cl l n a + cl l n b := by
  unfold cl
  calc ⌈(((a + b) * n : ℕ) : ℚ) / l⌉₊ = ⌈((a * n : ℕ) : ℚ) / l + ((b * n : ℕ) : ℚ) / l⌉₊ := by
        congr 1; push_cast; ring
    _ ≤ _ := Nat.ceil_add_le _ _

lemma cl_add_l {l n : ℕ} (hl : 0 < l) (j : ℕ) : cl l n (j + l) = cl l n j + n := by
  unfold cl
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have : (((j + l) * n : ℕ) : ℚ) / l = ((j * n : ℕ) : ℚ) / l + (n : ℚ) := by
    push_cast; field_simp
  rw [this, Nat.ceil_add_natCast (by positivity)]

lemma cl_l {l n : ℕ} (hl : 0 < l) : cl l n l = n := by
  simpa [cl_zero] using cl_add_l (n := n) hl 0

lemma cl_mono (l n : ℕ) {a b : ℕ} (h : a ≤ b) : cl l n a ≤ cl l n b := by
  unfold cl
  apply Nat.ceil_mono
  gcongr

lemma cl_succ_le {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (j : ℕ) : cl l n (j + 1) ≤ cl l n j + 1 := by
  have h1 := cl_add_le l n j 1
  have h2 : cl l n 1 ≤ 1 := by rw [cl_le_iff hl]; omega
  omega

/-- The letter of `s̃` at position `i` (any `i : ℕ`, periodic of period `l`). -/
def wt (l n i : ℕ) : Bool := decide (cl l n i < cl l n (i + 1))

lemma wt_toNat {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (i : ℕ) :
    (wt l n i).toNat = cl l n (i + 1) - cl l n i := by
  unfold wt
  have h1 := cl_succ_le hl hn i
  have h2 := cl_mono l n (Nat.le_succ i)
  by_cases h : cl l n i < cl l n (i + 1)
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

lemma count_map_shift {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (m k : ℕ) :
    ((List.range k).map (fun i => wt l n (m + i))).count true = cl l n (m + k) - cl l n m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih]
    have h1 := cl_mono l n (Nat.le_add_right m k)
    have h2 := cl_mono l n (show m + k ≤ m + k + 1 by omega)
    have h3 := wt_toNat hl hn (m + k)
    have h4 : [wt l n (m + k)].count true = (wt l n (m + k)).toNat := by
      cases wt l n (m + k) <;> rfl
    simp only [List.map_cons, List.map_nil]
    rw [h4, h3, show m + (k + 1) = m + k + 1 by omega]
    omega

lemma wt_add_l {l n : ℕ} (hl : 0 < l) (i : ℕ) : wt l n (i + l) = wt l n i := by
  unfold wt
  rw [show i + l + 1 = (i + 1) + l by omega, cl_add_l hl, cl_add_l hl]
  simp

lemma wt_mod {l n : ℕ} (hl : 0 < l) (i : ℕ) : wt l n (i % l) = wt l n i := by
  conv_rhs => rw [← Nat.mod_add_div i l]
  generalize i / l = q
  induction q with
  | zero => simp
  | succ q ih => rw [show i % l + l * (q + 1) = (i % l + l * q) + l by ring, wt_add_l hl, ih]

lemma stilde_length (l n : ℕ) : (stilde l n).length = l := by simp [stilde]

lemma stilde_rotate {l n : ℕ} (hl : 0 < l) (m : ℕ) :
    (stilde l n).rotate m = (List.range l).map (fun i => wt l n (m + i)) := by
  apply List.ext_getElem
  · simp [stilde]
  · intro i h1 h2
    rw [List.getElem_rotate]
    simp only [stilde, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    rw [show (decide (cl l n ((i + m) % l) < cl l n ((i + m) % l + 1))) = wt l n ((i + m) % l) from rfl,
      wt_mod hl, Nat.add_comm i m]

lemma stilde_rot_prefix {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (m k : ℕ) (hk : k ≤ l) :
    (((stilde l n).rotate m).take k).count true = cl l n (m + k) - cl l n m := by
  rw [stilde_rotate hl, ← List.map_take, List.take_range, Nat.min_eq_left hk, count_map_shift hl hn]

lemma stilde_prefix {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) (k : ℕ) (hk : k ≤ l) :
    ((stilde l n).take k).count true = cl l n k := by
  have := stilde_rot_prefix hl hn 0 k hk
  rwa [List.rotate_zero, cl_zero, zero_add, Nat.sub_zero] at this

lemma stilde_count {l n : ℕ} (hl : 0 < l) (hn : n ≤ l) : (stilde l n).count true = n := by
  have := stilde_prefix hl hn l le_rfl
  rwa [List.take_of_length_le (stilde_length l n).le, cl_l hl] at this

lemma lemma4_weak (s t : List Bool) (hl : s.length = t.length) (hn : s.count true = t.count true)
    (hdom : ∀ k, 1 ≤ k → k ≤ s.length → (s.take k).count true ≤ (t.take k).count true) :
    phi t ≤ phi s := by
  by_cases h : s = t
  · subst h; exact le_rfl
  · exact (lemma4_thm s t hl hn h hdom).le

lemma rot_prefix (t : List Bool) (m k : ℕ) (hm : m ≤ t.length) (hk : k ≤ t.length) :
    ((t.rotate m).take k).count true + (t.take m).count true
      = (t.take (m + k)).count true + (t.take (m + k - t.length)).count true := by
  rw [List.rotate_eq_drop_append_take hm, List.take_append, List.take_take, List.count_append,
    List.length_drop]
  have h2 : min (k - (t.length - m)) m = m + k - t.length := by omega
  rw [h2]
  have h3 : (t.take (m + k)).count true = (t.take m).count true + ((t.drop m).take k).count true := by
    rw [List.take_add, List.count_append]
  omega

/-- The rotation chosen in the proof of Lemma 5 (the staircase touches the line `kn/l` from above). -/
lemma exists_good_rotation (t : List Bool) (hl : 0 < t.length) :
    ∃ m, 1 ≤ m ∧ m ≤ t.length ∧ ∀ k, 1 ≤ k → k ≤ t.length →
      cl t.length (t.count true) k ≤ ((t.rotate m).take k).count true := by
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 t.length)
    (fun j : ℕ => (j : ℤ) * t.count true - t.length * (t.take j).count true)
    ⟨t.length, Finset.mem_Icc.mpr ⟨hl, le_rfl⟩⟩
  have hm := Finset.mem_Icc.mp hmS
  have hP : ∀ j, t.length ≤ j → (t.take j).count true = t.count true := fun j hj => by
    rw [List.take_of_length_le hj]
  have hmax' : ∀ j, j ≤ t.length →
      (j : ℤ) * t.count true - t.length * (t.take j).count true
        ≤ (m : ℤ) * t.count true - t.length * (t.take m).count true := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have := hmax t.length (Finset.mem_Icc.mpr ⟨hl, le_rfl⟩)
      rw [hP _ le_rfl] at this
      simp only [List.take_zero, List.count_nil, Nat.cast_zero, zero_mul, mul_zero, sub_zero]
      linarith
    · exact hmax j (Finset.mem_Icc.mpr ⟨hj0, hj⟩)
  refine ⟨m, hm.1, hm.2, fun k hk1 hkl => ?_⟩
  rw [cl_le_iff hl]
  have hrp := rot_prefix t m k hm.2 hkl
  set c := ((t.rotate m).take k).count true with hc
  by_cases hmk : m + k ≤ t.length
  · have h0 : m + k - t.length = 0 := by omega
    rw [h0, List.take_zero, List.count_nil] at hrp
    have hmx := hmax' (m + k) hmk
    have hcz : (c : ℤ) = (t.take (m + k)).count true - (t.take m).count true := by omega
    zify
    rw [hcz]
    push_cast at hmx
    nlinarith
  · have hj : m + k - t.length ≤ t.length := by omega
    have hmx := hmax' (m + k - t.length) hj
    rw [hP (m + k) (by omega)] at hrp
    have hcz : (c : ℤ) = t.count true + (t.take (m + k - t.length)).count true - (t.take m).count true := by
      omega
    have hjz : ((m + k - t.length : ℕ) : ℤ) = m + k - t.length := by omega
    rw [hjz] at hmx
    zify
    rw [hcz]
    nlinarith

theorem lemma5_thm : lemma5 := by
  intro l n hl hn
  have hlen := stilde_length l n
  have hcount := stilde_count hl hn
  have hS : stilde l n ∈ Sln l n := ⟨hlen, hcount⟩
  have hA : ∀ m, phi (stilde l n) ≤ phi ((stilde l n).rotate m) := by
    intro m
    apply lemma4_weak
    · simp
    · exact (List.rotate_perm _ m).count_eq true
    · intro k _ hk2
      rw [List.length_rotate, hlen] at hk2
      rw [stilde_rot_prefix hl hn m k hk2, stilde_prefix hl hn k hk2]
      have := cl_add_le l n m k
      omega
  have hself : (stilde l n).rotate l = stilde l n := by
    have := List.rotate_length (stilde l n)
    rwa [hlen] at this
  have hleast : IsLeast (phi '' sigma (stilde l n)) (phi (stilde l n)) := by
    refine ⟨⟨stilde l n, ⟨l, hl, hlen.ge, hself.symm⟩, rfl⟩, ?_⟩
    rintro _ ⟨t, ⟨k, -, -, rfl⟩, rfl⟩
    exact hA k
  have hmin : minRot (stilde l n) = phi (stilde l n) := hleast.csInf_eq
  have hgreat : IsGreatest (minRot '' Sln l n) (phi (stilde l n)) := by
    refine ⟨⟨stilde l n, hS, hmin⟩, ?_⟩
    rintro _ ⟨t, ⟨htl, htn⟩, rfl⟩
    obtain ⟨m, hm1, hm2, hgood⟩ := exists_good_rotation t (by omega)
    rw [htl, htn] at hgood
    rw [htl] at hm2
    calc minRot t ≤ phi (t.rotate m) := Nat.sInf_le ⟨t.rotate m, ⟨m, hm1, by omega, rfl⟩, rfl⟩
      _ ≤ phi (stilde l n) := by
        apply lemma4_weak
        · simp [hlen, htl]
        · rw [hcount, (List.rotate_perm t m).count_eq true, htn]
        · intro k hk1 hk2
          rw [hlen] at hk2
          rw [stilde_prefix hl hn k hk2]
          exact hgood k hk1 hk2
  refine ⟨hlen, ?_, hS, hleast, hgreat, hmin.symm, ?_⟩
  · intro i hi
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
    simp only [stilde, List.getElem_map, List.getElem_range]
    exact wt_toNat hl hn i
  · rw [hmin]
    exact hgreat.csSup_eq.symm

theorem cor1_thm : cor1 := by
  intro l n hl hn
  obtain ⟨hlen, hval, -, -, -, h1, h2⟩ := lemma5_thm l n hl hn
  rw [← h2, ← h1, eq3_thm, hlen, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [hval j hj']
  have hdrop : ((stilde l n).drop (j + 1)).count true = n - cl l n (j + 1) := by
    have := count_take_add_drop (stilde l n) (j + 1)
    rw [stilde_prefix hl hn (j + 1) (by omega), stilde_count hl hn] at this
    omega
  rw [hdrop, show 1 + j - 1 = j by omega, show 1 + j = j + 1 by omega]
  ring

/-! ## (13) and Lemma 9 -/

lemma rotR_append (u : List Bool) (b : Bool) : rotR (u ++ [b]) = b :: u := by
  unfold rotR
  rw [show (u ++ [b]).length - 1 = u.length by simp]
  exact List.rotate_append_length_eq u [b]

theorem eq13_thm : eq13 := by
  intro u
  refine ⟨rotR_append u false, rotR_append u true, ?_, ?_⟩
  · rw [phi_cons, phi_append_false]
    simp
  · rw [phi_cons, phi_append_true]
    simp only [List.count_append, List.count_singleton_self, List.length_append, List.length_singleton,
      ↓reduceIte]
    push_cast
    ring

lemma phi_rotR_true_int (u : List Bool) :
    3 * (phi (true :: u) : ℤ) = 2 * phi (u ++ [true]) - d (u ++ [true]) := by
  rw [phi_cons, phi_append_true]
  simp only [LaboBP.d, List.count_append, List.count_singleton_self, List.length_append,
    List.length_singleton, ↓reduceIte]
  push_cast
  ring

lemma d_rotate (s : List Bool) (k : ℕ) : d (s.rotate k) = d s := by
  unfold LaboBP.d
  rw [List.length_rotate, (List.rotate_perm s k).count_eq]

lemma three_not_dvd_phi_true (u : List Bool) : ¬ (3 : ℤ) ∣ (phi (u ++ [true]) : ℤ) := by
  rw [phi_append_true]
  push_cast
  intro h
  have h2 : (3 : ℤ) ∣ 2 ^ u.length := (dvd_add_right (dvd_mul_right 3 _)).mp h
  have h3 := Int.prime_three.dvd_of_dvd_pow h2
  norm_num at h3

lemma int_gcd_congr {a b c : ℤ} (h1 : ∀ k : ℤ, k ∣ a → k ∣ b → k ∣ c)
    (h2 : ∀ k : ℤ, k ∣ a → k ∣ c → k ∣ b) : Int.gcd a b = Int.gcd a c := by
  apply Nat.dvd_antisymm
  · exact Int.dvd_gcd (Int.gcd_dvd_left a b) (h1 _ (Int.gcd_dvd_left a b) (Int.gcd_dvd_right a b))
  · exact Int.dvd_gcd (Int.gcd_dvd_left a c) (h2 _ (Int.gcd_dvd_left a c) (Int.gcd_dvd_right a c))

theorem lemma9_14_gen_thm : lemma9_14_gen := by
  intro u
  rw [rotR_append]
  have hrel := phi_rotR_true_int u
  have h3 := three_not_dvd_phi_true u
  apply int_gcd_congr
  · intro k hx hy
    have hd : d (u ++ [true]) = 2 * (phi (u ++ [true]) : ℤ) - 3 * phi (true :: u) := by linarith
    rw [hd]
    exact dvd_sub (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _)
  · intro k hx hd
    have hk3 : IsCoprime k 3 :=
      (Int.prime_three.coprime_iff_not_dvd.mpr h3).symm.of_isCoprime_of_dvd_left hx
    have h3y : k ∣ 3 * (phi (true :: u) : ℤ) := by
      rw [hrel]
      exact dvd_sub (dvd_mul_of_dvd_right hx _) hd
    exact hk3.dvd_of_dvd_mul_left h3y

theorem lemma9_14_thm : lemma9_14 := by
  intro s u _ hu _
  obtain ⟨k, -, -, hk⟩ := hu
  rw [lemma9_14_gen_thm u, hk, d_rotate]

lemma rotR_rotate (s : List Bool) (r : ℕ) :
    rotR (s.rotate (r * (s.length - 1))) = s.rotate ((r + 1) * (s.length - 1)) := by
  unfold rotR
  rw [List.length_rotate, List.rotate_rotate]
  congr 1
  ring

lemma rot_reach (s : List Bool) (k : ℕ) :
    s.rotate (k * (s.length - 1) * (s.length - 1)) = s.rotate k := by
  rcases Nat.eq_zero_or_pos s.length with h0 | hpos
  · rw [List.length_eq_zero_iff.mp h0]
    simp
  rw [← List.rotate_mod s (k * _ * _), ← List.rotate_mod s k]
  congr 1
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [hm, Nat.succ_sub_one]
  rcases m with _ | p
  · simp only [Nat.succ_eq_add_one, Nat.zero_add, Nat.mod_one]
  · rw [show k * (p + 1) * (p + 1) = k + (p + 1 + 1) * (k * p) by ring, Nat.succ_eq_add_one,
      Nat.add_mul_mod_self_left]

/-- **The core of Lemma 9, from the kernel.**  Along the right shift ρ, (13) reads
`3^{[last]}·ϕ(ρw) = 2·ϕ(w) + C·(2^l − 3^n)`: a transport chain.  The kernel's
`collapse_of_recurrence`, applied to the modulus `e` (any divisor of `2^l − 3^n`), gives
`e ∣ ϕ(λ^k s) ↔ e ∣ ϕ(s)` for every rotation. -/
lemma core_dvd (s : List Bool) (hs : true ∈ s) (e : ℤ) (he : e ∣ d s) (k : ℕ) :
    e ∣ (phi (s.rotate k) : ℤ) ↔ e ∣ (phi s : ℤ) := by
  have hl : s.length ≠ 0 := (List.length_pos_of_mem hs).ne'
  have hn : s.count true ≠ 0 := (List.count_pos_iff.mpr hs).ne'
  obtain ⟨f, hf⟩ := he
  let L := s.length - 1
  let R : ℕ → ℤ := fun r => phi (s.rotate (r * L))
  let B : ℕ → Bool := fun r => (s.rotate (r * L)).getD L false
  have hrec : ∀ r, (3 : ℤ) ^ (B r).toNat * R (r + 1)
      = 2 ^ 1 * R r + ((if B r then -1 else 0) * f) * e := by
    intro r
    have hwl : (s.rotate (r * L)).length = s.length := List.length_rotate _ _
    obtain ⟨u, b, hub⟩ : ∃ u b, s.rotate (r * L) = u ++ [b] := by
      rcases List.eq_nil_or_concat (s.rotate (r * L)) with h | ⟨u, b, h⟩
      · exact absurd (by rw [← hwl, h]; rfl) hl
      · exact ⟨u, b, by rw [h, List.concat_eq_append]⟩
    have hul : u.length = L := by
      have := congrArg List.length hub
      simp only [List.length_append, List.length_singleton] at this
      omega
    have hB : B r = b := by
      simp only [B]
      rw [hub, ← hul]
      simp
    have hR1 : R (r + 1) = phi (b :: u) := by
      simp only [R]
      rw [← rotR_rotate, hub, rotR_append]
    have hR0 : R r = phi (u ++ [b]) := by simp only [R]; rw [hub]
    have hd : d (u ++ [b]) = d s := by rw [← hub, d_rotate]
    rw [hB, hR1, hR0]
    cases b
    · rw [phi_cons, phi_append_false]
      simp
    · have := phi_rotR_true_int u
      rw [hd, hf] at this
      simp only [Bool.toNat_true, pow_one, ↓reduceIte]
      linarith
  have hdvd : e ∣ (2 : ℤ) ^ s.length - 3 ^ s.count true := ⟨f, hf⟩
  have hcollapse := CollatzTransport.collapse_of_recurrence e R
    (fun r => (3 : ℤ) ^ (B r).toNat) (fun _ => (2 : ℤ) ^ 1) (fun r => (if B r then -1 else 0) * f)
    (fun r => (CollatzTransport.coprime_pow_three hn _).of_isCoprime_of_dvd_left hdvd)
    (fun _ => (CollatzTransport.coprime_pow_two hl 1).of_isCoprime_of_dvd_left hdvd)
    hrec
  have := hcollapse (k * L)
  simp only [R] at this
  rwa [rot_reach, zero_mul, List.rotate_zero] at this

lemma gcd_congr_right {a b c : ℤ} (h : ∀ e : ℤ, e ∣ c → (e ∣ a ↔ e ∣ b)) :
    Int.gcd a c = Int.gcd b c := by
  apply Nat.dvd_antisymm
  · exact Int.dvd_gcd ((h _ (Int.gcd_dvd_right a c)).mp (Int.gcd_dvd_left a c)) (Int.gcd_dvd_right a c)
  · exact Int.dvd_gcd ((h _ (Int.gcd_dvd_right b c)).mpr (Int.gcd_dvd_left b c)) (Int.gcd_dvd_right b c)

theorem lemma9_core_thm : lemma9_core :=
  fun s hs k => gcd_congr_right fun e he => core_dvd s hs e he k

theorem lemma9_15_gen_thm : lemma9_15_gen := by
  intro s hs
  have hl0 : 0 < s.length := List.length_pos_of_mem hs
  have hGall : ∀ j, (Finset.range s.length).gcd (fun k => (phi (s.rotate (k + 1)) : ℤ))
      ∣ (phi (s.rotate j) : ℤ) := by
    intro j
    have hj : s.rotate j = s.rotate ((j + s.length - 1) % s.length + 1) := by
      rw [← List.rotate_mod s j, ← List.rotate_mod s ((j + s.length - 1) % s.length + 1)]
      congr 1
      rw [Nat.mod_add_mod, Nat.sub_add_cancel (by omega : 1 ≤ j + s.length), Nat.add_mod_right]
    rw [hj]
    exact Finset.gcd_dvd (Finset.mem_range.mpr (Nat.mod_lt _ hl0))
  apply dvd_antisymm_of_normalize_eq Finset.normalize_gcd (normalize_gcd _ _)
  · apply dvd_gcd
    · simpa using hGall 0
    · obtain ⟨i, hi, hsi⟩ := List.mem_iff_getElem.mp hs
      set u := s.drop (i + 1) ++ s.take i with hu
      have ht : s.rotate (i + 1) = u ++ [true] := by
        rw [List.rotate_eq_drop_append_take (by omega), List.take_succ_eq_append_getElem hi, hsi, hu,
          List.append_assoc]
      have hrho : s.rotate (i + 1 + (s.length - 1)) = true :: u := by
        rw [← List.rotate_rotate, ht]
        have hr := rotR_append u true
        unfold rotR at hr
        rw [← hr]
        congr 1
        rw [← ht, List.length_rotate]
      have hrel := phi_rotR_true_int u
      rw [← ht, d_rotate, ← hrho] at hrel
      have hdq : d s = 2 * (phi (s.rotate (i + 1)) : ℤ) - 3 * phi (s.rotate (i + 1 + (s.length - 1))) := by
        linarith
      rw [hdq]
      exact dvd_sub (dvd_mul_of_dvd_right (hGall _) _) (dvd_mul_of_dvd_right (hGall _) _)
  · apply Finset.dvd_gcd
    intro k _
    have he : GCDMonoid.gcd (phi s : ℤ) (d s) ∣ d s := gcd_dvd_right _ _
    exact (core_dvd s hs _ he (k + 1)).mpr (gcd_dvd_left _ _)

theorem lemma9_15_thm : lemma9_15 := fun s hs _ => lemma9_15_gen_thm s hs

/-! ## Non-vacuity canaries (`decide`, kernel-evaluated; values predicted in labtrace id=445) -/

example : phi [true, false] = 1 := by decide
example : phi [true, true, false] = 5 ∧ d [true, true, false] = -1 := by decide
example : phi [true, true, false, true, false] = 23 := by decide
example : phi [false, false, false, false, true, true] = 80 ∧
    Int.gcd 80 (d [false, false, false, false, true, true]) = 5 := by decide
/-- The hypothesis `true ∈ s` of (15) is needed: on `s = 00` the gcd of the rotations is 0, but `gcd(ϕ(s), 2² − 1) = 3`. -/
example : (Finset.range 2).gcd (fun k => (phi ([false, false].rotate (k + 1)) : ℤ)) = 0 ∧
    GCDMonoid.gcd (phi [false, false] : ℤ) (d [false, false]) = 3 := by decide

end LaboHH
