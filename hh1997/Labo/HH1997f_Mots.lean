import Mathlib
import Labo.HH1997f_Enonces
import Labo.HH1997c_Preuves

/-!
# LABO-COLLATZ · HH1997f · formaliste (2026-10-19) — words: factorization of `s̃`, stability under concatenation

Part 1 of the proofs of `Labo/HH1997f_Enonces.lean`: `stilde_append`, `stilde_wpow`, `phi_lt_append`, and the
normalized quantities `f(w) = ϕ(w)/2^{l(w)}`, `g(w) = 3^{n(w)}/2^{l(w)}` with `f(uv) = g(v)f(u) + f(v)`,
`g(uv) = g(u)g(v)` (both are (4)).  Reused: `cl_le_iff`, `cl_zero`, `cl_add_l`, `cl_l`, `cl_mono`, `stilde_length`,
`stilde_count`, `eq4_thm` (batch a), `M_eq_phi_stilde`, `nOf_le`, `nOf_spec_thm`, `Q4_eq_M_thm` (batch b).
-/

namespace LaboHH

open LaboBP

/-! ## `s̃` of a concatenation -/

lemma stilde_getElem {l n i : ℕ} (hi : i < (stilde l n).length) :
    (stilde l n)[i] = decide (cl l n i < cl l n (i + 1)) := by
  simp [stilde]

/-- General criterion: if the ceilings of `(L, N)` restrict to those of `(l₁, n₁)` and, shifted, of `(l₂, n₂)`. -/
lemma stilde_append_of {L N l₁ n₁ l₂ n₂ : ℕ} (hL : L = l₁ + l₂)
    (h1 : ∀ j, j ≤ l₁ → cl L N j = cl l₁ n₁ j)
    (h2 : ∀ j, j ≤ l₂ → cl L N (l₁ + j) = n₁ + cl l₂ n₂ j) :
    stilde L N = stilde l₁ n₁ ++ stilde l₂ n₂ := by
  apply List.ext_getElem
  · simp [stilde_length, hL]
  · intro i hi hi'
    rw [stilde_getElem]
    by_cases hil : i < l₁
    · rw [List.getElem_append_left (by simpa [stilde_length] using hil), stilde_getElem,
        h1 i hil.le, h1 (i + 1) hil]
    · push Not at hil
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hil
      have hj : j < l₂ := by simp [stilde_length, hL] at hi; omega
      rw [List.getElem_append_right (by simp [stilde_length]), stilde_getElem]
      simp only [stilde_length, Nat.add_sub_cancel_left]
      rw [h2 j hj.le, show l₁ + j + 1 = l₁ + (j + 1) by omega, h2 (j + 1) hj]
      simp

/-- First segment of the Christoffel factorization. -/
lemma cl_seg1 {l₁ n₁ l₂ n₂ : ℕ} (h1 : 0 < l₁) (h2 : 0 < l₂) (hd : n₁ * l₂ = n₂ * l₁ + 1) {j : ℕ}
    (hj : j ≤ l₁) : cl (l₁ + l₂) (n₁ + n₂) j = cl l₁ n₁ j := by
  have hL : 0 < l₁ + l₂ := by omega
  have E : l₁ * (n₁ + n₂) + 1 = n₁ * (l₁ + l₂) := by nlinarith
  have e1 : j * (l₁ * (n₁ + n₂)) + j = j * (n₁ * (l₁ + l₂)) := by rw [← E]; ring
  apply le_antisymm
  · rw [cl_le_iff hL]
    have hc := (cl_le_iff (n := n₁) (j := j) h1).mp le_rfl
    have e2 : j * n₁ * (l₁ + l₂) ≤ cl l₁ n₁ j * l₁ * (l₁ + l₂) := Nat.mul_le_mul_right _ hc
    have key : l₁ * (j * (n₁ + n₂)) ≤ l₁ * (cl l₁ n₁ j * (l₁ + l₂)) := by nlinarith
    exact Nat.le_of_mul_le_mul_left key h1
  · rw [cl_le_iff h1]
    have hc := (cl_le_iff (n := n₁ + n₂) (j := j) hL).mp le_rfl
    set c := cl (l₁ + l₂) (n₁ + n₂) j
    have e2 : l₁ * (j * (n₁ + n₂)) ≤ l₁ * (c * (l₁ + l₂)) := Nat.mul_le_mul_left _ hc
    have key : j * n₁ * (l₁ + l₂) < (c * l₁ + 1) * (l₁ + l₂) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right key
    omega

/-- Second segment of the Christoffel factorization. -/
lemma cl_seg2 {l₁ n₁ l₂ n₂ : ℕ} (h1 : 0 < l₁) (h2 : 0 < l₂) (hd : n₁ * l₂ = n₂ * l₁ + 1) {j : ℕ}
    (hj : j ≤ l₂) : cl (l₁ + l₂) (n₁ + n₂) (l₁ + j) = n₁ + cl l₂ n₂ j := by
  have hL : 0 < l₁ + l₂ := by omega
  have E2 : l₂ * (n₁ + n₂) = (l₁ + l₂) * n₂ + 1 := by nlinarith
  have hge : n₁ ≤ cl (l₁ + l₂) (n₁ + n₂) (l₁ + j) := by
    calc n₁ = cl l₁ n₁ l₁ := (cl_l h1).symm
      _ = cl (l₁ + l₂) (n₁ + n₂) l₁ := (cl_seg1 h1 h2 hd le_rfl).symm
      _ ≤ _ := cl_mono _ _ (by omega)
  have f1 : l₂ * ((l₁ + j) * (n₁ + n₂)) = (l₁ + j) * ((l₁ + l₂) * n₂ + 1) := by rw [← E2]; ring
  have f2 : ∀ d, l₂ * ((n₁ + d) * (l₁ + l₂)) = (n₂ * l₁ + 1) * (l₁ + l₂) + d * l₂ * (l₁ + l₂) := by
    intro d; rw [← hd]; ring
  apply le_antisymm
  · rw [cl_le_iff hL]
    have hc := (cl_le_iff (n := n₂) (j := j) h2).mp le_rfl
    have f3 : j * n₂ * (l₁ + l₂) ≤ cl l₂ n₂ j * l₂ * (l₁ + l₂) := Nat.mul_le_mul_right _ hc
    have key : l₂ * ((l₁ + j) * (n₁ + n₂)) ≤ l₂ * ((n₁ + cl l₂ n₂ j) * (l₁ + l₂)) := by
      rw [f1, f2]; nlinarith
    exact Nat.le_of_mul_le_mul_left key h2
  · obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le hge
    rw [hd']
    apply Nat.add_le_add_left
    rw [cl_le_iff h2]
    have hc := (cl_le_iff (n := n₁ + n₂) (j := l₁ + j) hL).mp le_rfl
    rw [hd'] at hc
    have e := Nat.mul_le_mul_left l₂ hc
    rw [f1, f2] at e
    have key : j * n₂ * (l₁ + l₂) < (d * l₂ + 1) * (l₁ + l₂) := by nlinarith
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right key)

theorem stilde_append_thm : stilde_append := fun _ _ _ _ h1 h2 hd =>
  stilde_append_of rfl (fun _ hj => cl_seg1 h1 h2 hd hj) (fun _ hj => cl_seg2 h1 h2 hd hj)

/-! ## Copies: `s̃(kl, kn) = s̃(l,n)^k` -/

lemma wpow_zero (w : List Bool) : wpow w 0 = [] := rfl

lemma wpow_succ (w : List Bool) (k : ℕ) : wpow w (k + 1) = w ++ wpow w k := by
  simp [wpow, List.replicate_succ]

lemma wpow_succ' (w : List Bool) (k : ℕ) : wpow w (k + 1) = wpow w k ++ w := by
  simp [wpow, List.replicate_succ']

lemma cl_mul {k l n : ℕ} (hk : 0 < k) (hl : 0 < l) (j : ℕ) : cl (k * l) (k * n) j = cl l n j := by
  have hkl : 0 < k * l := Nat.mul_pos hk hl
  apply le_antisymm
  · rw [cl_le_iff hkl]
    have hc := (cl_le_iff (n := n) (j := j) hl).mp le_rfl
    calc j * (k * n) = k * (j * n) := by ring
      _ ≤ k * (cl l n j * l) := Nat.mul_le_mul_left _ hc
      _ = cl l n j * (k * l) := by ring
  · rw [cl_le_iff hl]
    have hc := (cl_le_iff (n := k * n) (j := j) hkl).mp le_rfl
    have : k * (j * n) ≤ k * (cl (k * l) (k * n) j * l) := by
      calc k * (j * n) = j * (k * n) := by ring
        _ ≤ cl (k * l) (k * n) j * (k * l) := hc
        _ = k * (cl (k * l) (k * n) j * l) := by ring
    exact Nat.le_of_mul_le_mul_left this hk

lemma cl_add_mul {l n : ℕ} (hl : 0 < l) (j k : ℕ) : cl l n (j + k * l) = cl l n j + k * n := by
  induction k with
  | zero => simp
  | succ k ih => rw [show j + (k + 1) * l = (j + k * l) + l by ring, cl_add_l hl, ih]; ring

theorem stilde_wpow_thm : stilde_wpow := by
  intro k l n hl
  induction k with
  | zero => simp [stilde, wpow]
  | succ k ih =>
    rw [wpow_succ', ← ih]
    apply stilde_append_of (by ring)
    · intro j hj
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have : j = 0 := by simpa using hj
        subst this
        simp [cl_zero]
      · rw [cl_mul (by omega) hl, cl_mul hk hl]
    · intro j _
      rw [cl_mul (by omega) hl, show k * l + j = j + k * l by ring, cl_add_mul hl]
      ring

/-- `s̃(l_u + k l_v, n_u + k n_v) = s̃(u) s̃(v)^k` when `n_u l_v − n_v l_u = 1`. -/
lemma stilde_append_wpow {lu nu lv nv : ℕ} (hu : 0 < lu) (hv : 0 < lv) (hd : nu * lv = nv * lu + 1) (k : ℕ) :
    stilde (lu + k * lv) (nu + k * nv) = stilde lu nu ++ wpow (stilde lv nv) k := by
  induction k with
  | zero => simp [wpow]
  | succ k ih =>
    rw [show lu + (k + 1) * lv = (lu + k * lv) + lv by ring, show nu + (k + 1) * nv = (nu + k * nv) + nv by ring,
      stilde_append_thm _ _ _ _ (by positivity) hv (by nlinarith), ih, wpow_succ', List.append_assoc]

/-- `s̃(k l_v + l_u, k n_v + n_u) = s̃(v)^k s̃(u)` when `n_v l_u − n_u l_v = 1`. -/
lemma stilde_wpow_append {lu nu lv nv : ℕ} (hu : 0 < lu) (hv : 0 < lv) (hd : nv * lu = nu * lv + 1) (k : ℕ) :
    stilde (k * lv + lu) (k * nv + nu) = wpow (stilde lv nv) k ++ stilde lu nu := by
  induction k with
  | zero => simp [wpow]
  | succ k ih =>
    rw [show (k + 1) * lv + lu = lv + (k * lv + lu) by ring, show (k + 1) * nv + nu = nv + (k * nv + nu) by ring,
      stilde_append_thm _ _ _ _ hv (by positivity) (by nlinarith), ih, wpow_succ, List.append_assoc]

/-! ## (4) and the inequality `ϕ < B (2^l − 3^n)` -/

lemma phi_append_q (u v : List Bool) :
    (phi (u ++ v) : ℚ) = 3 ^ v.count true * phi u + 2 ^ u.length * phi v := by
  rw [eq4_thm u v]; push_cast; ring

theorem phi_lt_append_thm : phi_lt_append := by
  intro B u v hu hv
  rw [phi_append_q, List.length_append, List.count_append, pow_add, pow_add]
  have h1 := mul_lt_mul_of_pos_left hu (by positivity : (0 : ℚ) < 3 ^ v.count true)
  have h2 := mul_lt_mul_of_pos_left hv (by positivity : (0 : ℚ) < 2 ^ u.length)
  nlinarith [h1, h2]

/-- `ϕ(w) < B (2^{l(w)} − 3^{n(w)})`. -/
def good (B : ℚ) (w : List Bool) : Prop := (phi w : ℚ) < B * ((2 : ℚ) ^ w.length - 3 ^ w.count true)

lemma good_append {B : ℚ} {u v : List Bool} (hu : good B u) (hv : good B v) : good B (u ++ v) :=
  phi_lt_append_thm B u v hu hv

lemma good_wpow {B : ℚ} {w : List Bool} (h : good B w) : ∀ k, 0 < k → good B (wpow w k)
  | 0, hk => absurd hk (lt_irrefl 0)
  | 1, _ => by simpa [wpow] using h
  | k + 2, _ => by rw [wpow_succ']; exact good_append (good_wpow h (k + 1) (by omega)) h

lemma good_append_wpow {B : ℚ} {u v : List Bool} (hu : good B u) (hv : good B v) (k : ℕ) :
    good B (u ++ wpow v k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [wpow] using hu
  · exact good_append hu (good_wpow hv k hk)

/-! ## Normalized quantities `f = ϕ/2^l`, `g = 3^n/2^l` -/

/-- `f(w) = ϕ(w)/2^{l(w)}`. -/
def fw (w : List Bool) : ℚ := phi w / 2 ^ w.length

/-- `g(w) = 3^{n(w)}/2^{l(w)}`. -/
def gw (w : List Bool) : ℚ := 3 ^ w.count true / 2 ^ w.length

lemma fw_append (u v : List Bool) : fw (u ++ v) = gw v * fw u + fw v := by
  unfold fw gw
  rw [phi_append_q, List.length_append, pow_add]
  field_simp

lemma gw_append (u v : List Bool) : gw (u ++ v) = gw u * gw v := by
  unfold gw
  rw [List.length_append, List.count_append, pow_add, pow_add]
  field_simp

lemma fw_nonneg (w : List Bool) : 0 ≤ fw w := by unfold fw; positivity

lemma gw_pos (w : List Bool) : 0 < gw w := by unfold gw; positivity

lemma good_iff {B : ℚ} {w : List Bool} : good B w ↔ fw w < B * (1 - gw w) := by
  unfold good fw gw
  have h : (0 : ℚ) < 2 ^ w.length := by positivity
  rw [show B * (1 - 3 ^ w.count true / 2 ^ w.length) = B * (2 ^ w.length - 3 ^ w.count true) / 2 ^ w.length by
    field_simp, div_lt_div_iff_of_pos_right h]

lemma gw_wpow (w : List Bool) (k : ℕ) : gw (wpow w k) = gw w ^ k := by
  induction k with
  | zero => simp [wpow, gw]
  | succ k ih => rw [wpow_succ', gw_append, ih, pow_succ]

lemma fw_wpow (w : List Bool) (k : ℕ) : fw (wpow w k) = fw w * ∑ i ∈ Finset.range k, gw w ^ i := by
  induction k with
  | zero => simp [wpow, fw]
  | succ k ih =>
    rw [wpow_succ', fw_append, ih, Finset.sum_range_succ', pow_zero]
    simp only [pow_succ, ← Finset.sum_mul]
    ring

/-! ## From words to `Q4` -/

lemma Q4_lt_of_good {B : ℚ} {l n : ℕ} (hl : 0 < l) (hn : nOf l = n) (hg : good B (stilde l n)) : Q4 l < B := by
  have hnl : n ≤ l := hn ▸ nOf_le l
  have h3 : 3 ^ n < 2 ^ l := hn ▸ (nOf_spec_thm l hl).1
  have h3' : (3 : ℚ) ^ n < 2 ^ l := by exact_mod_cast h3
  have hD : (0 : ℚ) < 2 ^ l - 3 ^ n := by linarith
  rw [Q4_eq_M_thm l hl, hn, M_eq_phi_stilde hl hnl, div_lt_iff₀ hD]
  unfold good at hg
  rw [stilde_length, stilde_count hl hnl] at hg
  linarith

lemma le_Q4_of {B : ℚ} {l n : ℕ} (hl : 0 < l) (hn : nOf l = n)
    (hg : B * ((2 : ℚ) ^ l - 3 ^ n) ≤ phi (stilde l n)) : B ≤ Q4 l := by
  have hnl : n ≤ l := hn ▸ nOf_le l
  have h3 : 3 ^ n < 2 ^ l := hn ▸ (nOf_spec_thm l hl).1
  have h3' : (3 : ℚ) ^ n < 2 ^ l := by exact_mod_cast h3
  have hD : (0 : ℚ) < 2 ^ l - 3 ^ n := by linarith
  rw [Q4_eq_M_thm l hl, hn, M_eq_phi_stilde hl hnl, le_div_iff₀ hD]
  exact hg

/-- `n(l) = n` from `3^n < 2^l < 3^{n+1}` in ℚ. -/
lemma nOf_of_q {l n : ℕ} (hl : 0 < l) (h1 : (3 : ℚ) ^ n < 2 ^ l) (h2 : (2 : ℚ) ^ l < 3 ^ (n + 1)) : nOf l = n :=
  nOf_eq hl (by exact_mod_cast h1) (by exact_mod_cast h2)

end LaboHH
