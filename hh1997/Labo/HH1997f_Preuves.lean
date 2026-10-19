import Mathlib
import Labo.HH1997f_Calcul

/-!
# LABO-COLLATZ · HH1997f · formaliste (2026-10-19) — PROOFS of `Labo/HH1997f_Enonces.lean` (assembly)

Part 3: `M_half` (Prop. 1 + Bernoulli), the lattice argument behind the Second step (every `l < p₁₈` at once, no
loop), the exceptional lengths, and `example44_check`, hence `example44` (with `example44_reduction_thm`, batch c),
and the optimality `example44_Lm`.  Axiom log: `Labo/HH1997f_Axiomes.lean`.

The lattice argument.  With `(P, Q) = (p₁₆, q₁₆)`, `(P', Q') = (p₁₇, q₁₇)` (paper's index), `PQ' − P'Q = 1`, every pair
`(l, n(l))` is `a(P, Q) − c(P', Q')` with integers `a = lQ' − nP'`, `c = Ql − Pn`, and
`2^l/3^n = X^a Y^c`, `X = 2^P/3^Q ≥ 1 + α`, `Y = 3^{Q'}/2^{P'} ≥ 1 + β` (kernel-certified in `HH1997f_Calcul`).
`c < 0` is impossible; `c = 0` gives `l ∈ {P, 2P, …, 5P}`; `c = 1, a = 10` gives `l = 5P + p₁₄`; in every other case
Bernoulli and a linear inequality in `(a, c)` give `2m·3^n < (2m − n)·2^l`.
-/

namespace LaboHH

open LaboBP

/-! ## Prop. 1 at `n = n(l)` with Bernoulli -/

lemma bern_bound {l : ℕ} (hl : 0 < l) :
    (nOf l : ℝ) / l * (1 / (2 - (3 : ℝ) ^ ((nOf l : ℝ) / l)))
      ≤ nOf l * 2 ^ l / (2 * ((2 : ℝ) ^ l - 3 ^ nOf l)) := by
  set n := nOf l
  have h3 : 3 ^ n < 2 ^ l := (nOf_spec_thm l hl).1
  have h3R : (3 : ℝ) ^ n < 2 ^ l := by exact_mod_cast h3
  have hD : (0 : ℝ) < 2 ^ l - 3 ^ n := by linarith
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hr2 := rr_lt_two hl h3
  have hrl := rr_pow_l n hl
  have hp : (0 : ℝ) < 2 ^ l := by positivity
  have hb := one_add_mul_le_pow (a := -(1 - rr l n / 2)) (by linarith [rr_pos l n]) l
  rw [show (1 : ℝ) + -(1 - rr l n / 2) = rr l n / 2 by ring, div_pow, hrl] at hb
  have hb' := (le_div_iff₀ hp).mp hb
  have h2D : 2 * (2 ^ l - 3 ^ n) ≤ l * 2 ^ l * (2 - rr l n) := by nlinarith
  have hpos : (0 : ℝ) < l * (2 - rr l n) := mul_pos hlR (by linarith)
  have e : (n : ℝ) / l * (1 / (2 - (3 : ℝ) ^ ((n : ℝ) / l))) = n / (l * (2 - rr l n)) := by
    unfold rr; field_simp
  rw [e, div_le_div_iff₀ hpos (by positivity)]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem M_half_thm : M_half := by
  intro l hl
  set n := nOf l
  have h3 : 3 ^ n < 2 ^ l := (nOf_spec_thm l hl).1
  have h3R : (3 : ℝ) ^ n < 2 ^ l := by exact_mod_cast h3
  have hD : (0 : ℝ) < 2 ^ l - 3 ^ n := by linarith
  have h := (prop1_thm l n le_rfl).trans (bern_bound hl)
  rw [div_le_div_iff₀ hD (by positivity)] at h
  have h' : (2 * M l n : ℝ) * (2 ^ l - 3 ^ n) ≤ (n * 2 ^ l) * (2 ^ l - 3 ^ n) := by nlinarith
  have := le_of_mul_le_mul_right h' hD
  exact_mod_cast this

/-- From (★) to `Q4(l) < B`. -/
lemma Q4_lt_of_star {l B : ℕ} (hl : 0 < l) (hnB : nOf l ≤ 2 * B)
    (h : 2 * B * 3 ^ nOf l < (2 * B - nOf l) * 2 ^ l) : Q4 l < B := by
  set n := nOf l
  have h3 : 3 ^ n < 2 ^ l := (nOf_spec_thm l hl).1
  have h3Q : (3 : ℚ) ^ n < 2 ^ l := by exact_mod_cast h3
  have hD : (0 : ℚ) < 2 ^ l - 3 ^ n := by linarith
  have hM : (2 * M l n : ℚ) ≤ n * 2 ^ l := by exact_mod_cast M_half_thm l hl
  have hQ : ((2 * B * 3 ^ n : ℕ) : ℚ) < (((2 * B - n) * 2 ^ l : ℕ) : ℚ) := by exact_mod_cast h
  push_cast [Nat.cast_sub hnB] at hQ
  rw [Q4_eq_M_thm l hl, div_lt_iff₀ hD]
  nlinarith

/-! ## The lattice argument (abstract `P, Q, P', Q'`: no huge power is ever evaluated) -/

set_option maxHeartbeats 1000000 in
lemma lattice {P Q P' Q' : ℕ} {α β B : ℚ} (hdet : P * Q' = P' * Q + 1) (hP : 0 < P)
    (hα : 0 ≤ α) (hβ : 0 < β)
    (hX : 1 + α ≤ (2 : ℚ) ^ P / 3 ^ Q) (hY : 1 + β ≤ (3 : ℚ) ^ Q' / 2 ^ P')
    (hNB : (P : ℚ) + P' < 2 * B)
    (hA : 0 < (Q : ℚ) - (2 * B - (P + P')) * α)
    (hE1 : 0 ≤ ((2 * B - (P + P')) * β + Q') * P - P' * (Q - (2 * B - (P + P')) * α))
    (hc2 : ((P : ℚ) + P') * (Q - (2 * B - (P + P')) * α)
      ≤ 2 * (((2 * B - (P + P')) * β + Q') * P - P' * (Q - (2 * B - (P + P')) * α)))
    (hc1 : 9 * ((Q : ℚ) - (2 * B - (P + P')) * α) < (2 * B - (P + P')) * β + Q')
    (h11 : P + 2 * P' < 11 * P)
    {l n : ℕ} (hl : 1 ≤ l) (hlN : l < P + P') (hnl : n ≤ l) (h3 : 3 ^ n < 2 ^ l) :
    (∃ a, l = a * P ∧ n = a * Q) ∨ (l + P' = 10 * P ∧ n + Q' = 10 * Q) ∨
      2 * B * (3 : ℚ) ^ n < (2 * B - n) * 2 ^ l := by
  have hdetZ : (P : ℤ) * Q' = P' * Q + 1 := by exact_mod_cast hdet
  set a : ℤ := (l : ℤ) * Q' - n * P' with ha
  set c : ℤ := (Q : ℤ) * l - P * n with hc
  have hla : (l : ℤ) = a * P - c * P' := by rw [ha, hc]; linear_combination (-(l : ℤ)) * hdetZ
  have hna : (n : ℤ) = a * Q - c * Q' := by rw [ha, hc]; linear_combination (-(n : ℤ)) * hdetZ
  have hPZ : (0 : ℤ) < P := by exact_mod_cast hP
  have hlZ : (1 : ℤ) ≤ l := by exact_mod_cast hl
  have hlNZ : (l : ℤ) < P + P' := by exact_mod_cast hlN
  -- the two convergents, in ℕ
  have hX1 : 3 ^ Q ≤ 2 ^ P := by
    have h0 : (0 : ℚ) < 3 ^ Q := by positivity
    have : (1 : ℚ) ≤ 2 ^ P / 3 ^ Q := by linarith
    rw [le_div_iff₀ h0, one_mul] at this
    exact_mod_cast this
  have hY1 : 2 ^ P' < 3 ^ Q' := by
    have h0 : (0 : ℚ) < 2 ^ P' := by positivity
    have : (1 : ℚ) < 3 ^ Q' / 2 ^ P' := by linarith
    rw [lt_div_iff₀ h0, one_mul] at this
    exact_mod_cast this
  rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
  · -- `c < 0`: impossible
    exfalso
    have hP'Z : (0 : ℤ) ≤ P' := by positivity
    have hcP : c * P' ≤ -1 * P' := mul_le_mul_of_nonneg_right (by omega) hP'Z
    have haP : a * P < 1 * P := by linarith
    have ha0 : a ≤ 0 := by have := lt_of_mul_lt_mul_right haP hPZ.le; omega
    obtain ⟨a', ha'⟩ : ∃ a' : ℕ, (a' : ℤ) = -a := ⟨(-a).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨c', hc'⟩ : ∃ c' : ℕ, (c' : ℤ) = -c := ⟨(-c).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hc'1 : 1 ≤ c' := by omega
    have e1 : l + a' * P = c' * P' := by
      have : ((l + a' * P : ℕ) : ℤ) = ((c' * P' : ℕ) : ℤ) := by push_cast; rw [ha', hc']; linarith
      exact_mod_cast this
    have e2 : n + a' * Q = c' * Q' := by
      have : ((n + a' * Q : ℕ) : ℤ) = ((c' * Q' : ℕ) : ℤ) := by push_cast; rw [ha', hc']; linarith
      exact_mod_cast this
    have k1 : 2 ^ l * 2 ^ (a' * P) < 3 ^ n * 2 ^ (a' * P) := by
      calc 2 ^ l * 2 ^ (a' * P) = (2 ^ P') ^ c' := by rw [← pow_add, e1, ← pow_mul, mul_comm]
        _ < (3 ^ Q') ^ c' := Nat.pow_lt_pow_left hY1 (by omega)
        _ = 3 ^ n * (3 ^ Q) ^ a' := by rw [← pow_mul, ← pow_mul, ← pow_add, mul_comm Q' c', mul_comm Q a', e2]
        _ ≤ 3 ^ n * (2 ^ P) ^ a' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX1 a')
        _ = 3 ^ n * 2 ^ (a' * P) := by rw [← pow_mul, mul_comm P a']
    have k2 : 3 ^ n * 2 ^ (a' * P) < 2 ^ l * 2 ^ (a' * P) := Nat.mul_lt_mul_of_pos_right h3 (by positivity)
    omega
  · -- `c = 0`: `l = aP`, `n = aQ`
    left
    have ha1 : 0 < a := by
      rw [hc0, zero_mul, sub_zero] at hla
      exact pos_of_mul_pos_left (by linarith : (0 : ℤ) < a * P) hPZ.le
    refine ⟨a.toNat, ?_, ?_⟩
    · have : (l : ℤ) = ((a.toNat * P : ℕ) : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg ha1.le, hla, hc0]; ring
      exact_mod_cast this
    · have : (n : ℤ) = ((a.toNat * Q : ℕ) : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg ha1.le, hna, hc0]; ring
      exact_mod_cast this
  · -- `c ≥ 1`
    have hP'Z : (0 : ℤ) ≤ P' := by positivity
    have ha1 : 0 < a := by
      have hcP : 0 ≤ c * P' := mul_nonneg hc0.le hP'Z
      exact pos_of_mul_pos_left (by linarith : (0 : ℤ) < a * P) hPZ.le
    obtain ⟨an, han⟩ : ∃ an : ℕ, (an : ℤ) = a := ⟨a.toNat, Int.toNat_of_nonneg ha1.le⟩
    obtain ⟨cn, hcn⟩ : ∃ cn : ℕ, (cn : ℤ) = c := ⟨c.toNat, Int.toNat_of_nonneg hc0.le⟩
    have hcn1 : 1 ≤ cn := by omega
    have e1 : l + cn * P' = an * P := by
      have : ((l + cn * P' : ℕ) : ℤ) = ((an * P : ℕ) : ℤ) := by push_cast; rw [han, hcn]; linarith
      exact_mod_cast this
    have e2 : n + cn * Q' = an * Q := by
      have : ((n + cn * Q' : ℕ) : ℤ) = ((an * Q : ℕ) : ℤ) := by push_cast; rw [han, hcn]; linarith
      exact_mod_cast this
    by_cases hmid : cn = 1 ∧ an = 10
    · right; left
      obtain ⟨rfl, rfl⟩ := hmid
      omega
    right; right
    -- rational versions
    have e1Q : (l : ℚ) + cn * P' = an * P := by exact_mod_cast e1
    have e2Q : (n : ℚ) + cn * Q' = an * Q := by exact_mod_cast e2
    have hlNQ : (l : ℚ) < P + P' := by exact_mod_cast hlN
    have hnlQ : (n : ℚ) ≤ l := by exact_mod_cast hnl
    have hPQ : (0 : ℚ) < P := by exact_mod_cast hP
    have hP'Q : (0 : ℚ) ≤ P' := by positivity
    set A' : ℚ := Q - (2 * B - (P + P')) * α with hA'
    set B' : ℚ := (2 * B - (P + P')) * β + Q' with hB'
    -- the linear certificate: `a A' < c B'`
    have hlin : (an : ℚ) * A' < cn * B' := by
      have hanP : (an : ℚ) * P < P + (cn + 1) * P' := by linarith
      rcases Nat.eq_or_lt_of_le hcn1 with h1 | h2
      · -- `c = 1`, so `a ≤ 9`
        subst h1
        have han10 : an ≠ 10 := fun h => hmid ⟨rfl, h⟩
        have han11 : an * P < 11 * P := by
          have : an * P < P + 2 * P' := by omega
          omega
        have han9 : an ≤ 9 := by
          have := Nat.lt_of_mul_lt_mul_right han11
          omega
        have : (an : ℚ) ≤ 9 := by exact_mod_cast han9
        simp only [Nat.cast_one, one_mul]
        linarith [mul_le_mul_of_nonneg_right this hA.le]
      · -- `c ≥ 2`
        have hc2' : (2 : ℚ) ≤ cn := by exact_mod_cast h2
        have k1 : (an : ℚ) * P * A' < (P + (cn + 1) * P') * A' := mul_lt_mul_of_pos_right hanP hA
        have k0 : 2 * (B' * P - P' * A') ≤ cn * (B' * P - P' * A') := mul_le_mul_of_nonneg_right hc2' hE1
        have k2 : (P + (cn + 1) * P') * A' ≤ cn * B' * P := by linarith
        have k3 := lt_of_lt_of_le k1 k2
        rw [show (an : ℚ) * P * A' = (an * A') * P by ring, show (cn : ℚ) * B' * P = (cn * B') * P by ring] at k3
        exact lt_of_mul_lt_mul_right k3 hPQ.le
    -- Bernoulli
    have hXa : 1 + an * α ≤ ((2 : ℚ) ^ P / 3 ^ Q) ^ an :=
      le_trans (one_add_mul_le_pow (by linarith) an) (pow_le_pow_left₀ (by linarith) hX an)
    have hYc : 1 + cn * β ≤ ((3 : ℚ) ^ Q' / 2 ^ P') ^ cn :=
      le_trans (one_add_mul_le_pow (by linarith) cn) (pow_le_pow_left₀ (by linarith) hY cn)
    have hx : (2 : ℚ) ^ l / 3 ^ n = ((2 : ℚ) ^ P / 3 ^ Q) ^ an * ((3 : ℚ) ^ Q' / 2 ^ P') ^ cn := by
      have f1 : (2 : ℚ) ^ (an * P) = 2 ^ l * 2 ^ (cn * P') := by rw [← pow_add, e1]
      have f2 : (3 : ℚ) ^ (an * Q) = 3 ^ n * 3 ^ (cn * Q') := by rw [← pow_add, e2]
      rw [div_pow, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm P an, mul_comm Q an,
        mul_comm Q' cn, mul_comm P' cn, f1, f2]
      field_simp
    have hα0 : (0 : ℚ) ≤ an * α := by positivity
    have hβ0 : (0 : ℚ) ≤ cn * β := by positivity
    have hxlow : 1 + an * α + cn * β ≤ (2 : ℚ) ^ l / 3 ^ n := by
      rw [hx]
      have h1 : (0 : ℚ) ≤ 1 + an * α := by linarith
      calc 1 + an * α + cn * β ≤ (1 + an * α) * (1 + cn * β) := by
            rw [show (1 + an * α) * (1 + cn * β) = 1 + an * α + cn * β + (an * α) * (cn * β) by ring]
            linarith [mul_nonneg hα0 hβ0]
        _ ≤ _ := mul_le_mul hXa hYc (by linarith) (le_trans h1 hXa)
    -- conclusion
    have hn2B : (n : ℚ) < 2 * B := by linarith
    have hq : (0 : ℚ) < 3 ^ n := by positivity
    have key : 2 * B < (2 * B - n) * ((2 : ℚ) ^ l / 3 ^ n) := by
      have k1 : (n : ℚ) < (2 * B - (P + P')) * (an * α + cn * β) := by
        have : (n : ℚ) = an * Q - cn * Q' := by linarith
        rw [this]
        rw [hA', hB'] at hlin
        linarith
      have k2 : (2 * B - (P + P')) * (an * α + cn * β) ≤ (2 * B - n) * (an * α + cn * β) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
      have k3 : (2 * B - n) * (1 + an * α + cn * β) ≤ (2 * B - n) * ((2 : ℚ) ^ l / 3 ^ n) :=
        mul_le_mul_of_nonneg_left hxlow (by linarith)
      linarith
    rw [mul_div_assoc', lt_div_iff₀ hq] at key
    exact key

/-! ## The Second step -/

lemma A6_sub (l : ℕ) (h : l ∈ A6) : l ∈ A12 := by
  simp only [A6, A12, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  omega

theorem example44_step2_star_thm : example44_step2_star := by
  intro l hl hlN hA6
  have h3 := (nOf_spec_thm l (by omega)).1
  rcases lattice (P := 17087915) (Q := 10781274) (P' := 85137581) (Q' := 53715833)
      (α := 115 / 10 ^ 10) (β := 34 / 10 ^ 10) (B := 212366032807211)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) X_ge Y_ge (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hl (by omega) (nOf_le l) h3 with
    ⟨a, hla, -⟩ | ⟨h1, -⟩ | h
  · exfalso
    apply hA6
    have : a ≤ 5 := by omega
    have : 1 ≤ a := by omega
    interval_cases a <;> simp [A6, hla]
  · exfalso
    apply hA6
    have : l = 85741569 := by omega
    simp [A6, this]
  · have hn : nOf l ≤ 2 * 212366032807211 := by have := nOf_le l; omega
    have h' : ((2 * 212366032807211 * 3 ^ nOf l : ℕ) : ℚ) < (((2 * 212366032807211 - nOf l) * 2 ^ l : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub hn]
      linarith
    exact_mod_cast h'

theorem example44_step2_thm : example44_step2 := by
  intro l hl1 hlN hA12
  have hl : 0 < l := by omega
  have hA6 : l ∉ A6 := fun h => hA12 (A6_sub l h)
  have hstar := example44_step2_star_thm l (by omega) hlN hA6
  set n := nOf l
  have h3 : 3 ^ n < 2 ^ l := (nOf_spec_thm l hl).1
  have h3R : (3 : ℝ) ^ n < 2 ^ l := by exact_mod_cast h3
  have hD : (0 : ℝ) < 2 * ((2 : ℝ) ^ l - 3 ^ n) := by linarith
  have hn : n ≤ 2 * 212366032807211 := by have := nOf_le l; omega
  have hR : ((2 * 212366032807211 * 3 ^ n : ℕ) : ℝ) < (((2 * 212366032807211 - n) * 2 ^ l : ℕ) : ℝ) := by
    exact_mod_cast hstar
  push_cast [Nat.cast_sub hn] at hR
  refine lt_of_le_of_lt (bern_bound hl) ?_
  rw [div_lt_iff₀ hD]
  linarith

/-! ## The Third step and the exceptional lengths -/

theorem example44_step3_thm : example44_step3 :=
  Q4_lt_of_good (by norm_num) nOf_p16 good_W15

lemma Q4_A1 (a : ℕ) (ha : 1 ≤ a) (ha5 : a ≤ 5) : Q4 (a * 17087915) < 212366032807211 := by
  apply Q4_lt_of_good (by omega) (nOf_A1 a ha ha5)
  rw [WA1_eq]
  exact good_wpow good_W15 a (by omega)

lemma Q4_A2 (k : ℕ) (hk5 : k ≤ 5) : Q4 (k * 17087915 + 301994) < 212366032807211 := by
  apply Q4_lt_of_good (by omega) (nOf_A2 k hk5)
  rw [WA2_eq]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [wpow] using good_W13
  · exact good_append (good_wpow good_W15 k hk) good_W13

theorem example44_A_thm : example44_A := by
  intro l hl
  simp only [A12, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Q4_A1 1 le_rfl (by norm_num)
  · simpa using Q4_A1 2 (by norm_num) (by norm_num)
  · simpa using Q4_A1 3 (by norm_num) (by norm_num)
  · simpa using Q4_A1 4 (by norm_num) (by norm_num)
  · simpa using Q4_A1 5 (by norm_num) (by norm_num)
  · simpa using Q4_A2 3 (by norm_num)
  · simpa using Q4_A2 4 (by norm_num)
  · simpa using Q4_A2 5 (by norm_num)

/-! ## The Fourth step: the finite check, the example, the optimality -/

theorem example44_check_thm : example44_check := by
  intro l hl hlN
  by_cases h : l ∈ A6
  · exact example44_A_thm l (A6_sub l h)
  · have hn : nOf l ≤ 2 * 212366032807211 := by have := nOf_le l; omega
    exact_mod_cast Q4_lt_of_star (B := 212366032807211) (by omega) hn (example44_step2_star_thm l hl hlN h)

theorem example44_thm : example44 := example44_reduction_thm example44_check_thm

theorem example44_Lm_thm : example44_Lm := by
  unfold example44_Lm Lm
  apply le_antisymm
  · exact Nat.sInf_le Q4_pN
  · have hne : ({L : ℕ | (212366032807211 : ℚ) ≤ Q4 L}).Nonempty := ⟨102225496, Q4_pN⟩
    apply le_csInf hne
    intro L hL
    simp only [Set.mem_ofPred_eq] at hL
    by_contra hlt
    push Not at hlt
    rcases Nat.eq_zero_or_pos L with rfl | hL0
    · have : Q4 0 = 0 := by simp [Q4]
      rw [this] at hL
      norm_num at hL
    · exact absurd hL (not_le.mpr (example44_check_thm L hL0 hlt))

end LaboHH
