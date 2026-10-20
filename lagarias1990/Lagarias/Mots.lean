import Mathlib
import Lagarias.L1990b_Enonces
import Lagarias.L4_Preuves

/-!
# Lagarias 1990 · primitive words (the combinatorics behind (2.4)–(2.5))

Mathlib v4.34 has neither primitive words, nor Lyndon words, nor necklaces. This file builds what (2.4) needs,
for words over `Bool`, with `List.rotate` and `Irred` exactly as in the frozen statements:

* `cyc v j = v_{j mod |v|}` reads a word cyclically; `v.rotate i = v` iff `cyc v` is `i`-periodic (`rot_iff`);
* the periods of a word are closed under `gcd` (`rot_gcd`), so its least period divides its length
  (`least_period`);
* `pw u n` is the word `u u u …` cut at length `n`, i.e. `u^{n/|u|}` when `|u| ∣ n`; it has the same periods
  as `u` (`rot_pw_iff`);
* every word of length `n` is `pw u n` for exactly one irreducible `u` of length `d ∣ n`
  (`words_eq_biUnion`, `pw_inj`), hence `Σ_{d∣n} #Irr(d) = 2ⁿ` (`sum_card_Irr`);
* rotation acts freely on irreducible words of length `d`: each orbit has `d` elements (`card_orb`), so
  `d ∣ #Irr(d)` (`dvd_card_Irr`).
-/

namespace Lagarias

open LaboBP LaboHH

/-! ## Cyclic reading -/

/-- Reading `v` cyclically: position `j` is `v_{j mod |v|}`. -/
def cyc (v : List Bool) (j : ℕ) : Bool := v.getD (j % v.length) false

lemma cyc_lt {v : List Bool} {j : ℕ} (h : j < v.length) : cyc v j = v[j] := by
  unfold cyc; rw [Nat.mod_eq_of_lt h, List.getD_eq_getElem _ _ h]

lemma cyc_rotate (v : List Bool) (i j : ℕ) : cyc (v.rotate i) j = cyc v (j + i) := by
  rcases Nat.eq_zero_or_pos v.length with h0 | hpos
  · rw [List.length_eq_zero_iff] at h0
    subst h0; simp [cyc]
  · have hl : (v.rotate i).length = v.length := List.length_rotate _ _
    have hj : j % v.length < v.length := Nat.mod_lt _ hpos
    unfold cyc
    rw [hl, List.getD_eq_getElem _ _ (by rw [hl]; exact hj), List.getElem_rotate,
      List.getD_eq_getElem _ _ (Nat.mod_lt _ hpos)]
    simp only [Nat.mod_add_mod]

lemma eq_of_cyc {v w : List Bool} (hl : v.length = w.length) (h : ∀ j, cyc v j = cyc w j) : v = w :=
  List.ext_getElem hl fun k h1 h2 => by rw [← cyc_lt h1, ← cyc_lt h2, h]

/-- `i` is a period of `v` iff the cyclic reading of `v` is `i`-periodic. -/
lemma rot_iff (v : List Bool) (i : ℕ) : v.rotate i = v ↔ ∀ j, cyc v (j + i) = cyc v j := by
  constructor
  · intro h j; rw [← cyc_rotate, h]
  · intro h
    apply List.ext_getElem (List.length_rotate _ _)
    intro k h1 h2
    rw [← cyc_lt h1, ← cyc_lt h2, cyc_rotate, h]

/-! ## Periods -/

lemma rot_mul {v : List Bool} {i : ℕ} (h : v.rotate i = v) (q : ℕ) : v.rotate (i * q) = v := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← List.rotate_rotate, ih, h]

lemma rot_mod {v : List Bool} {i j : ℕ} (hi : v.rotate i = v) (hj : v.rotate j = v) :
    v.rotate (j % i) = v := by
  have e : j = i * (j / i) + j % i := (Nat.div_add_mod j i).symm
  rw [e, ← List.rotate_rotate, rot_mul hi] at hj
  exact hj

/-- The periods of a word are closed under `gcd`. -/
lemma rot_gcd {v : List Bool} {i j : ℕ} (hi : v.rotate i = v) (hj : v.rotate j = v) :
    v.rotate (Nat.gcd i j) = v := by
  induction i, j using Nat.gcd.induction with
  | H0 n => simpa using hj
  | H1 m n _ ih => rw [Nat.gcd_rec]; exact ih (rot_mod hi hj) hi

/-- The least period `p` of a nonempty word: it divides the length, and no smaller positive shift fixes it. -/
lemma least_period (v : List Bool) (h : v ≠ []) :
    ∃ p, 0 < p ∧ p ∣ v.length ∧ v.rotate p = v ∧ ∀ i, 0 < i → i < p → v.rotate i ≠ v := by
  classical
  have hn : 0 < v.length := List.length_pos_iff.mpr h
  have hex : ∃ i, 0 < i ∧ v.rotate i = v := ⟨v.length, hn, List.rotate_length v⟩
  obtain ⟨hp0, hp⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hp0, ?_, hp, fun i hi hip hv => Nat.find_min hex hip ⟨hi, hv⟩⟩
  have hg := rot_gcd hp (List.rotate_length v)
  have hg0 : 0 < Nat.gcd (Nat.find hex) v.length := Nat.gcd_pos_of_pos_left _ hp0
  have hgle : Nat.gcd (Nat.find hex) v.length ≤ Nat.find hex := Nat.le_of_dvd hp0 (Nat.gcd_dvd_left _ _)
  have hnlt : ¬ Nat.gcd (Nat.find hex) v.length < Nat.find hex := fun hlt => Nat.find_min hex hlt ⟨hg0, hg⟩
  rw [← le_antisymm hgle (not_lt.mp hnlt)]
  exact Nat.gcd_dvd_right _ _

/-- In an irreducible word, a positive period dividing the length is the length. -/
lemma irred_period {u : List Bool} (hu : Irred u) (hn : 0 < u.length) {g : ℕ} (hg0 : 0 < g)
    (hgd : g ∣ u.length) (hr : u.rotate g = u) : g = u.length := by
  by_contra hne
  exact hu g (Finset.mem_Ico.mpr ⟨hg0, lt_of_le_of_ne (Nat.le_of_dvd hn hgd) hne⟩) hr

/-! ## Powers of a word -/

/-- `u u u …` cut at length `n` (that is `u^{n/|u|}` when `|u| ∣ n`). -/
def pw (u : List Bool) (n : ℕ) : List Bool := (List.range n).map (cyc u)

@[simp] lemma length_pw (u : List Bool) (n : ℕ) : (pw u n).length = n := by simp [pw]

lemma cyc_pw {u : List Bool} {n : ℕ} (hn : 0 < n) (hd : u.length ∣ n) (j : ℕ) :
    cyc (pw u n) j = cyc u j := by
  have hj : j % n < (pw u n).length := by rw [length_pw]; exact Nat.mod_lt _ hn
  conv_lhs => unfold cyc
  rw [length_pw, List.getD_eq_getElem _ _ (by rw [length_pw]; exact Nat.mod_lt _ hn)]
  simp only [pw, List.getElem_map, List.getElem_range]
  unfold cyc
  rw [Nat.mod_mod_of_dvd _ hd]

/-- `pw u n` has the same periods as `u`. -/
lemma rot_pw_iff {u : List Bool} {n : ℕ} (hn : 0 < n) (hd : u.length ∣ n) (i : ℕ) :
    (pw u n).rotate i = pw u n ↔ u.rotate i = u := by
  rw [rot_iff, rot_iff]; simp only [cyc_pw hn hd]

lemma take_pw {u : List Bool} {n : ℕ} (h : u.length ≤ n) : (pw u n).take u.length = u := by
  apply List.ext_getElem (by simp [h])
  intro k h1 h2
  rw [List.getElem_take]
  simp only [pw, List.getElem_map, List.getElem_range]
  exact cyc_lt h2

/-- A word with period `p ∣ |v|` is the power of its first `p` letters. -/
lemma eq_pw {v : List Bool} {p : ℕ} (hp : 0 < p) (hn : 0 < v.length) (hpn : p ∣ v.length)
    (h : v.rotate p = v) : v = pw (v.take p) v.length := by
  have hle : p ≤ v.length := Nat.le_of_dvd hn hpn
  have ht : (v.take p).length = p := by simp [hle]
  apply eq_of_cyc (length_pw _ _).symm
  intro j
  rw [cyc_pw hn (ht.symm ▸ hpn)]
  have e1 : cyc v j = cyc v (j % p) := by
    have := (rot_iff v (p * (j / p))).mp (rot_mul h _) (j % p)
    rwa [Nat.mod_add_div] at this
  have hj : j % p < p := Nat.mod_lt _ hp
  rw [e1, cyc_lt (lt_of_lt_of_le hj hle)]
  unfold cyc
  rw [ht, List.getD_eq_getElem _ _ (by rw [ht]; exact hj), List.getElem_take]

/-! ## Every word is a power of exactly one irreducible word -/

/-- The irreducible words of length `d` (the set counted by `Iirr`). -/
def Irr (d : ℕ) : Finset (List Bool) := (words d).filter Irred

lemma mem_Irr {d : ℕ} {u : List Bool} : u ∈ Irr d ↔ u.length = d ∧ Irred u := by
  simp [Irr, mem_words]

lemma Iirr_eq (d : ℕ) : Iirr d = (Irr d).card / d := rfl

/-- Uniqueness of the irreducible root. -/
lemma pw_inj {u u' : List Bool} {n : ℕ} (hn : 0 < n) (hu : Irred u) (hu' : Irred u')
    (hd : u.length ∣ n) (hd' : u'.length ∣ n) (h0 : 0 < u.length) (h0' : 0 < u'.length)
    (h : pw u n = pw u' n) : u = u' := by
  have h1 : (pw u n).rotate u.length = pw u n := (rot_pw_iff hn hd _).mpr (List.rotate_length u)
  have h2 : (pw u n).rotate u'.length = pw u n := by
    rw [h]; exact (rot_pw_iff hn hd' _).mpr (List.rotate_length u')
  have hg := rot_gcd h1 h2
  have hg0 : 0 < Nat.gcd u.length u'.length := Nat.gcd_pos_of_pos_left _ h0
  have e1 := irred_period hu h0 hg0 (Nat.gcd_dvd_left _ _) ((rot_pw_iff hn hd _).mp hg)
  have e2 := irred_period hu' h0' hg0 (Nat.gcd_dvd_right _ _) ((rot_pw_iff hn hd' _).mp (h ▸ hg))
  have hl : u.length = u'.length := e1.symm.trans e2
  have hle : u.length ≤ n := Nat.le_of_dvd hn hd
  rw [← take_pw hle, h, hl, take_pw (hl ▸ hle)]

lemma words_eq_biUnion {n : ℕ} (hn : 0 < n) :
    words n = n.divisors.biUnion (fun d => (Irr d).image (fun u => pw u n)) := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_image, mem_words, Nat.mem_divisors, mem_Irr]
  constructor
  · intro hv
    have hne : v ≠ [] := by rintro rfl; simp at hv; omega
    obtain ⟨p, hp0, hpd, hpr, hmin⟩ := least_period v hne
    have hvn : 0 < v.length := by omega
    have hle : p ≤ v.length := Nat.le_of_dvd hvn hpd
    have ht : (v.take p).length = p := by simp [hle]
    have hpw : v = pw (v.take p) v.length := eq_pw hp0 hvn hpd hpr
    refine ⟨p, ⟨hv ▸ hpd, hn.ne'⟩, v.take p, ⟨ht, ?_⟩, ?_⟩
    · intro i hi hrot
      rw [Finset.mem_Ico, ht] at hi
      apply hmin i hi.1 hi.2
      rw [hpw]
      exact (rot_pw_iff hvn (ht.symm ▸ hpd) i).mpr hrot
    · rw [← hv]; exact hpw.symm
  · rintro ⟨d, -, u, -, rfl⟩
    exact length_pw _ _

/-- The words form of (2.4): `Σ_{d∣n} #Irr(d) = 2ⁿ`. -/
theorem sum_card_Irr {n : ℕ} (hn : 0 < n) : ∑ d ∈ n.divisors, (Irr d).card = 2 ^ n := by
  rw [← card_words n, words_eq_biUnion hn, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [Finset.card_image_of_injOn]
    intro u hu u' hu' h
    rw [Finset.mem_coe, mem_Irr] at hu hu'
    have hdn := Nat.dvd_of_mem_divisors hd
    exact pw_inj hn hu.2 hu'.2 (hu.1 ▸ hdn) (hu'.1 ▸ hdn) (hu.1 ▸ hd0) (hu'.1 ▸ hd0) h
  · intro d hd d' hd' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨u', hu', h⟩ := Finset.mem_image.mp hw'
    rw [mem_Irr] at hu hu'
    rw [Finset.mem_coe] at hd hd'
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0' : 0 < d' := Nat.pos_of_mem_divisors hd'
    have := pw_inj hn hu'.2 hu.2 (hu'.1 ▸ Nat.dvd_of_mem_divisors hd') (hu.1 ▸ Nat.dvd_of_mem_divisors hd)
      (hu'.1 ▸ hd0') (hu.1 ▸ hd0) h
    exact hne (hu.1.symm.trans (this ▸ hu'.1))

/-! ## Rotations act freely on irreducible words -/

/-- The rotations of `u`. -/
def orb (u : List Bool) : Finset (List Bool) := (Finset.range u.length).image (u.rotate ·)

lemma rotate_irred {u : List Bool} (hu : Irred u) (k : ℕ) : Irred (u.rotate k) := by
  intro i hi h
  rw [List.length_rotate] at hi
  apply hu i hi
  rw [List.rotate_rotate, Nat.add_comm, ← List.rotate_rotate] at h
  exact List.rotate_eq_rotate.mp h

lemma card_orb {u : List Bool} (hu : Irred u) : (orb u).card = u.length := by
  rw [orb, Finset.card_image_of_injOn, Finset.card_range]
  have key : ∀ i j, i < j → j < u.length → u.rotate i ≠ u.rotate j := by
    intro i j hij hj h
    apply hu (j - i) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    apply List.rotate_eq_rotate (n := i) |>.mp
    rw [List.rotate_rotate, Nat.sub_add_cancel hij.le, h]
  intro i hi j hj h
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h (key i j hij hj)
  · exact hij
  · exact absurd h.symm (key j i hij hi)

lemma orb_sub {u w : List Bool} (hw : w ∈ orb u) : orb w ⊆ orb u := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  rw [Finset.mem_range] at hk
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  rw [List.rotate_rotate, ← List.rotate_mod]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩

lemma mem_orb_self {u : List Bool} (h : 0 < u.length) : u ∈ orb u :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr h, List.rotate_zero u⟩

/-- `d ∣ #Irr(d)` for `d > 0`: the irreducible words of length `d` fall into rotation orbits of size `d`.
(For `d = 0` the empty word is vacuously irreducible and `#Irr(0) = 1`.) -/
theorem dvd_card_Irr {d : ℕ} (hd : 0 < d) : d ∣ (Irr d).card := by
  rw [Finset.card_eq_sum_card_image orb (Irr d)]
  apply Finset.dvd_sum
  intro o ho
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ho
  rw [mem_Irr] at hu
  have hfib : (Irr d).filter (fun a => orb a = orb u) = orb u := by
    ext w
    rw [Finset.mem_filter, mem_Irr]
    constructor
    · rintro ⟨⟨hwl, -⟩, hwo⟩
      rw [← hwo]; exact mem_orb_self (hwl ▸ hd)
    · intro hw
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hw
      have hwI := rotate_irred hu.2 k
      refine ⟨⟨by rw [List.length_rotate, hu.1], hwI⟩, Finset.eq_of_subset_of_card_le (orb_sub hw) ?_⟩
      rw [card_orb hu.2, card_orb hwI, List.length_rotate]
  rw [hfib, card_orb hu.2, hu.1]

/-- `d · I(d) = #Irr(d)` for `d > 0`. -/
lemma mul_Iirr {d : ℕ} (hd : 0 < d) : d * Iirr d = (Irr d).card := Nat.mul_div_cancel' (dvd_card_Irr hd)

end Lagarias
