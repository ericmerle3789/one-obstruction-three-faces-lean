/-
T1Structure.lean — T1 (structure of survivors), the ceiling half, kernel-checked.
Session 2026-07-25, A.R.E.S. protocol (Merle side).

T1 is the "no-hair theorem" for Collatz cycles: a surviving positive cycle has no freedom
of shape. This file proves its FIRST half at the kernel, in pure integers (no logarithm):
for any positive cycle with p+1 odd elements all ≥ X, if 2(p+1) < 3X then
    3^(p+1) < 2^K < 2·3^(p+1)   —   i.e. K = ⌈(p+1)·log₂3⌉, the CEILING is forced.

Chain: (a) cycle product identity ∏(3xᵢ+1) = 2^K·∏xᵢ (telescoping);
(b) survivor bound (per-factor (3x+1)(3X) ≤ 3x(3X+1) ⟺ X ≤ x);
(c) binomial two-bound (m+1)^n < 2·m^n for 2n < m (elementary induction).
Machine-verified first (REQ-MATH-052): identity exact on all four real cycles (both shores),
bound+ceiling on the trivial cycle, 114 census cells consistent, Legendre window 3.5035491e10
(exact; integral form 3.503177115e10 — the earlier 4.955e10 was withdrawn at REQ-MATH-054),
and the GRID half (Ostrowski: ε-small n use only large convergent denominators) —
script-verified, NOT proved here.
-/
import Mathlib
import LegendreApprox

namespace T1Structure

/-- **(a) Cycle product identity**: `∏(3xᵢ+1) = 2^(Σvᵢ)·∏xᵢ`. -/
theorem cycle_prod_identity (p : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1)) :
    ∏ i, (3 * x i + 1) = 2 ^ (∑ i, v i) * ∏ i, x i := by
  calc ∏ i, (3 * x i + 1)
      = ∏ i, (2 ^ v i * x (i + 1)) := Finset.prod_congr rfl (fun i _ => hstep i)
    _ = (∏ i, 2 ^ v i) * ∏ i, x (i + 1) := Finset.prod_mul_distrib
    _ = 2 ^ (∑ i, v i) * ∏ i, x (i + 1) := by rw [Finset.prod_pow_eq_pow_sum]
    _ = 2 ^ (∑ i, v i) * ∏ i, x i := by
        congr 1
        exact Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun i => rfl)

/-- Two-bound, multiplied form: `m·(m+1)^n ≤ m^(n+1) + 2n·m^n` for `2n ≤ m`. -/
lemma mul_pow_succ_le (m : ℕ) : ∀ n, 2 * n ≤ m → m * (m+1) ^ n ≤ m ^ (n+1) + 2 * n * m ^ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro h
      have hn : 2 * n ≤ m := by omega
      have H := ih hn
      have key : 2 * n * m ^ n ≤ m ^ (n+1) := by
        calc 2 * n * m ^ n ≤ m * m ^ n := Nat.mul_le_mul_right _ hn
          _ = m ^ (n+1) := (pow_succ' m n).symm
      calc m * (m+1) ^ (n+1) = (m * (m+1) ^ n) * (m+1) := by ring
        _ ≤ (m ^ (n+1) + 2 * n * m ^ n) * (m+1) := Nat.mul_le_mul_right _ H
        _ = m ^ (n+2) + m ^ (n+1) + 2 * n * m ^ (n+1) + 2 * n * m ^ n := by ring
        _ ≤ m ^ (n+2) + m ^ (n+1) + 2 * n * m ^ (n+1) + m ^ (n+1) :=
            Nat.add_le_add_left key _
        _ = m ^ (n+2) + 2 * (n+1) * m ^ (n+1) := by ring

/-- **(c) Strict two-bound**: `(m+1)^n < 2·m^n` when `2n < m`. -/
lemma pow_succ_lt_two_mul_pow (m n : ℕ) (hm : 0 < m) (h : 2 * n < m) :
    (m+1) ^ n < 2 * m ^ n := by
  have H := mul_pow_succ_le m n (le_of_lt h)
  have hs : 2 * n * m ^ n < m * m ^ n :=
    Nat.mul_lt_mul_of_lt_of_le h (le_refl _) (pow_pos hm n)
  have hs' : 2 * n * m ^ n < m ^ (n+1) := by
    calc 2 * n * m ^ n < m * m ^ n := hs
      _ = m ^ (n+1) := (pow_succ' m n).symm
  have hlt : m * (m+1) ^ n < m * (2 * m ^ n) := by
    calc m * (m+1) ^ n ≤ m ^ (n+1) + 2 * n * m ^ n := H
      _ < m ^ (n+1) + m ^ (n+1) := Nat.add_lt_add_left hs' _
      _ = m * (2 * m ^ n) := by rw [pow_succ' m n]; ring
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- **(b) Survivor bound**: if every element is `≥ X`, then
    `2^K·(3X)^(p+1) ≤ 3^(p+1)·(3X+1)^(p+1)`. -/
theorem survivor_bound (p X K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hX : 0 < X) (hmin : ∀ i, X ≤ x i) :
    2 ^ K * (3 * X) ^ (p+1) ≤ 3 ^ (p+1) * (3 * X + 1) ^ (p+1) := by
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le hX (hmin i)
  have hprodpos : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hxpos i)
  have hfac : ∀ i, (3 * x i + 1) * (3 * X) ≤ (3 * x i) * (3 * X + 1) := by
    intro i; have := hmin i; nlinarith
  have hcard : (Finset.univ : Finset (Fin (p+1))).card = p + 1 := by
    simp
  have H : (∏ i, (3 * x i + 1)) * (3 * X) ^ (p+1)
      ≤ (∏ i, (3 * x i)) * (3 * X + 1) ^ (p+1) := by
    calc (∏ i, (3 * x i + 1)) * (3 * X) ^ (p+1)
        = ∏ i, ((3 * x i + 1) * (3 * X)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
      _ ≤ ∏ i, ((3 * x i) * (3 * X + 1)) :=
          Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => hfac i)
      _ = (∏ i, (3 * x i)) * (3 * X + 1) ^ (p+1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have hid : (∏ i, (3 * x i + 1)) = 2 ^ K * ∏ i, x i := by
    rw [hK]; exact cycle_prod_identity p x v hstep
  have h3 : (∏ i, (3 * x i)) = 3 ^ (p+1) * ∏ i, x i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  rw [hid, h3] at H
  refine Nat.le_of_mul_le_mul_left ?_ hprodpos
  calc (∏ i, x i) * (2 ^ K * (3 * X) ^ (p+1))
      = 2 ^ K * (∏ i, x i) * (3 * X) ^ (p+1) := by ring
    _ ≤ 3 ^ (p+1) * (∏ i, x i) * (3 * X + 1) ^ (p+1) := H
    _ = (∏ i, x i) * (3 ^ (p+1) * (3 * X + 1) ^ (p+1)) := by ring

/-- **THE CEILING (T1, first half).** A positive cycle whose elements all exceed `2(p+1)/3`
    has `2^K < 2·3^(p+1)`; with `q > 0` this pins `K = ⌈(p+1)·log₂3⌉`, in integer form. -/
theorem ceiling_upper (p X K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hX : 0 < X) (hmin : ∀ i, X ≤ x i)
    (hpX : 2 * (p+1) < 3 * X) :
    2 ^ K < 2 * 3 ^ (p+1) := by
  by_contra hcon
  push_neg at hcon
  have hb := survivor_bound p X K x v hstep hK hX hmin
  have h1 : 2 * 3 ^ (p+1) * (3 * X) ^ (p+1) ≤ 3 ^ (p+1) * (3 * X + 1) ^ (p+1) :=
    le_trans (Nat.mul_le_mul_right _ hcon) hb
  have h2 : 2 * (3 * X) ^ (p+1) ≤ (3 * X + 1) ^ (p+1) := by
    refine Nat.le_of_mul_le_mul_left ?_ (pow_pos (by norm_num : (0:ℕ) < 3) (p+1))
    calc 3 ^ (p+1) * (2 * (3 * X) ^ (p+1)) = 2 * 3 ^ (p+1) * (3 * X) ^ (p+1) := by ring
      _ ≤ 3 ^ (p+1) * (3 * X + 1) ^ (p+1) := h1
  have h3 : (3 * X + 1) ^ (p+1) < 2 * (3 * X) ^ (p+1) :=
    pow_succ_lt_two_mul_pow (3 * X) (p+1) (by positivity) hpX
  omega

/- ===== Canaries : le cycle trivial instancie tout ===== -/

/-- **The ceiling, lower half (REQ-MATH-066).** Found missing by Macindoe's round-10 audit:
`ceiling_upper` proves only `2^K < 2*3^(p+1)`; the companion bound `3^(p+1) < 2^K` was
threaded downstream as the hypothesis `hceil` and proved nowhere. One line from the product
identity: every factor `3*x i + 1` strictly exceeds `3*x i`, so
`3^(p+1) * ∏x < ∏(3x+1) = 2^K * ∏x`, and `∏x > 0` cancels. -/
theorem ceiling_lower (p X K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hX : 0 < X) (hmin : ∀ i, X ≤ x i) :
    3 ^ (p+1) < 2 ^ K := by
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le hX (hmin i)
  have hprodpos : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hxpos i)
  have hid : ∏ i, (3 * x i + 1) = 2 ^ K * ∏ i, x i := by
    rw [hK]; exact cycle_prod_identity p x v hstep
  have hL : ∏ i, (3 * x i) = 3 ^ (p+1) * ∏ i, x i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hlt : ∏ i, (3 * x i) < ∏ i, (3 * x i + 1) := by
    refine Finset.prod_lt_prod_of_nonempty (fun i _ => ?_) (fun i _ => ?_) Finset.univ_nonempty
    · have := hxpos i; omega
    · omega
  rw [hL, hid] at hlt
  exact lt_of_mul_lt_mul_right hlt (Nat.zero_le _)

/-- **The ceiling, both halves.** `K` is pinned: `3^(p+1) < 2^K < 2*3^(p+1)`. -/
theorem ceiling_pinned (p X K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hX : 0 < X) (hmin : ∀ i, X ≤ x i)
    (hpX : 2 * (p+1) < 3 * X) :
    3 ^ (p+1) < 2 ^ K ∧ 2 ^ K < 2 * 3 ^ (p+1) :=
  ⟨ceiling_lower p X K x v hstep hK hX hmin,
   ceiling_upper p X K x v hstep hK hX hmin hpX⟩

/-- Canary: `ceiling_pinned` on the trivial cycle gives `3 < 4 < 6`. -/
example : (3:ℕ) ^ 1 < 2 ^ 2 ∧ (2:ℕ) ^ 2 < 2 * 3 ^ 1 := by norm_num


/-- Canary: the trivial cycle (x ≡ 1, v ≡ 2 on Fin 1) satisfies the step hypothesis. -/
example : ∀ i : Fin 1, 3 * (fun _ : Fin 1 => 1) i + 1
    = 2 ^ (fun _ : Fin 1 => 2) i * (fun _ : Fin 1 => 1) (i + 1) := by
  intro i; norm_num

/-- Canary: instantiating `ceiling_upper` on the trivial cycle yields `2^2 < 2·3`. -/
example : (2:ℕ) ^ 2 < 2 * 3 ^ 1 :=
  ceiling_upper 0 1 2 (fun _ => 1) (fun _ => 2)
    (fun i => by norm_num) (by simp) (by norm_num) (fun i => le_refl 1) (by norm_num)

/-- Difference of powers, multiplied form (no subtraction):
    `(b+1)^(n+1) ≤ b^(n+1) + (n+1)·(b+1)^n`. -/
lemma succ_pow_le_pow_add (b : ℕ) : ∀ n, (b+1) ^ (n+1) ≤ b ^ (n+1) + (n+1) * (b+1) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hmono : b ^ (n+1) ≤ (b+1) ^ (n+1) := Nat.pow_le_pow_left (by omega) _
      calc (b+1) ^ (n+2) = (b+1) ^ (n+1) * (b+1) := by ring
        _ ≤ (b ^ (n+1) + (n+1) * (b+1) ^ n) * (b+1) := Nat.mul_le_mul_right _ ih
        _ = b ^ (n+1) * b + b ^ (n+1) + (n+1) * (b+1) ^ (n+1) := by ring
        _ ≤ b ^ (n+1) * b + (b+1) ^ (n+1) + (n+1) * (b+1) ^ (n+1) :=
            Nat.add_le_add_right (Nat.add_le_add_left hmono _) _
        _ = b ^ (n+2) + (n+2) * (b+1) ^ (n+1) := by ring

/-- **T1 grid half, quantitative core (the seam bound).** For a positive cycle with all
    elements ≥ X and `2p < 3X`:  `2^K·3X < 3^(p+1)·(3X + 2(p+1))`.
    Reading: `(2^K − 3^(p+1))·3X < 2(p+1)·3^(p+1)` — the seam gap `q` is squeezed inversely
    to the minimum element. Large `X` forces `‖n·log₂3‖ ≤ 2n/(3X·ln2)`; by best approximation
    (script-verified exhaustively, REQ-MATH-053; not formalized here) this confines `n` to
    the Ostrowski grid of convergent denominators and yields `n ≥ q₂₂ = 6.547·10¹⁰` for
    `X ≥ 2⁷¹` — one convergent step below Hercher's underlying `q₂₃ = 1.375·10¹¹`.
    Indexing pinned to `q₀ = q₁ = 1` both counted (OUT-054/056): `q₂₁ = 6586818670`,
    `q₂₂ = 65470613321`, `q₂₃ = 137528045312`. The `δ` above carries the factor 2 of
    REQ-MATH-054; the subscripts and the pre-054 `δ` were corrected 2026-07-29 after
    Macindoe's round-11 audit found two different `q₂₁` in this file. -/
theorem seam_bound (p X K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hX : 0 < X) (hmin : ∀ i, X ≤ x i)
    (hpX : 2 * p < 3 * X) :
    2 ^ K * (3 * X) < 3 ^ (p+1) * (3 * X + 2 * (p+1)) := by
  have hb := survivor_bound p X K x v hstep hK hX hmin
  have hd : (3*X+1) ^ (p+1) ≤ (3*X) ^ (p+1) + (p+1) * (3*X+1) ^ p :=
    succ_pow_le_pow_add (3*X) p
  have h2 : (3*X+1) ^ p < 2 * (3*X) ^ p :=
    pow_succ_lt_two_mul_pow (3*X) p (by positivity) hpX
  have hstep2 : (3*X+1) ^ (p+1) < (3*X) ^ (p+1) + (p+1) * (2 * (3*X) ^ p) := by
    calc (3*X+1) ^ (p+1) ≤ (3*X) ^ (p+1) + (p+1) * (3*X+1) ^ p := hd
      _ < (3*X) ^ (p+1) + (p+1) * (2 * (3*X) ^ p) :=
          Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left h2 (Nat.succ_pos p)) _
  have hfinal : (2 ^ K * (3 * X)) * (3 * X) ^ p
      < (3 ^ (p+1) * (3 * X + 2 * (p+1))) * (3 * X) ^ p := by
    calc (2 ^ K * (3 * X)) * (3 * X) ^ p
        = 2 ^ K * (3 * X) ^ (p+1) := by rw [pow_succ' (3*X) p]; ring
      _ ≤ 3 ^ (p+1) * (3 * X + 1) ^ (p+1) := hb
      _ < 3 ^ (p+1) * ((3*X) ^ (p+1) + (p+1) * (2 * (3*X) ^ p)) :=
          Nat.mul_lt_mul_of_pos_left hstep2 (pow_pos (by norm_num) _)
      _ = (3 ^ (p+1) * (3 * X + 2 * (p+1))) * (3 * X) ^ p := by
          rw [pow_succ' (3*X) p]; ring
  exact lt_of_mul_lt_mul_right hfinal (Nat.zero_le _)

/-- Canary: the trivial cycle instantiates the seam bound — `2^2·3 < 3·5`. -/
example : (2:ℕ) ^ 2 * 3 < 3 ^ 1 * 5 :=
  seam_bound 0 1 2 (fun _ => 1) (fun _ => 2)
    (fun i => by norm_num) (by simp) (by norm_num) (fun i => le_refl 1) (by norm_num)

/-- **March 1, arithmetic core.** Specialising the seam bound at the Barina threshold
    `X ≥ 2^71`: the seam gap of any surviving positive cycle is crushed below
    `3^(p+1)` by a factor `3·2^71 / (2(p+1))`.

    Stated subtraction-free (`q = 2^K − 3^(p+1)` is not formed): the hypothesis
    `2^K·(3·2^71) < 3^(p+1)·(3·2^71) + 3^(p+1)·2(p+1)` is exactly `q·3X < 2(p+1)·3^(p+1)`.

    This is the integer half of March 1. The analytic half — converting this into
    `‖(p+1)·log₂3‖ < (p+1)·δ` with `δ = 2/(3·2^71·ln 2)`, then invoking Legendre's
    criterion (contrapositive already available as `LegendreApprox.abs_sub_ge_of_not_convergent`,
    0 sorry / 0 axioms, in the Merle Junction repository) to force `K/(p+1)` to be a
    convergent, then checking the 22 convergent denominators below the Legendre window
    `3.5035·10^10` — is verified exactly in REQ-MATH-054 (all 22 fail the constraint, the
    tightest by a factor 5.4) but is **not formalized here**. -/
theorem seam_gap_at_barina (p K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hmin : ∀ i, 2 ^ 71 ≤ x i)
    (hpX : 2 * p < 3 * 2 ^ 71) :
    2 ^ K * (3 * 2 ^ 71) < 3 ^ (p+1) * (3 * 2 ^ 71) + 3 ^ (p+1) * (2 * (p+1)) := by
  have h := seam_bound p (2 ^ 71) K x v hstep hK (by positivity) hmin hpX
  calc 2 ^ K * (3 * 2 ^ 71)
      < 3 ^ (p+1) * (3 * 2 ^ 71 + 2 * (p+1)) := h
    _ = 3 ^ (p+1) * (3 * 2 ^ 71) + 3 ^ (p+1) * (2 * (p+1)) := by ring

/-- Canary: the trivial cycle does *not* satisfy the Barina hypothesis (its elements are 1),
    so the specialisation is not vacuously about it — the statement bites only above 2^71. -/
example : ¬ (∀ i : Fin 1, (2:ℕ) ^ 71 ≤ (fun _ : Fin 1 => 1) i) := by
  intro h; have := h 0; norm_num at this

/-! ### The analytic bridge (March 1-bis)

From the integer seam gap to the logarithmic gap, using only `Real.log_le_sub_one_of_pos`
(`log x ≤ x − 1`, Mathlib) — no continued fractions yet. This is the exact hinge feeding
Legendre's criterion. -/

/-- **The ratio bound.** For a surviving positive cycle at the Barina threshold:
    `1 < 2^K / 3^(p+1) < 1 + 2(p+1)/(3·2^71)`. -/
theorem ratio_bound_at_barina (p K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hmin : ∀ i, 2 ^ 71 ≤ x i)
    (hpX : 2 * p < 3 * 2 ^ 71) :
    1 < (2:ℝ) ^ K / 3 ^ (p+1) ∧
      (2:ℝ) ^ K / 3 ^ (p+1) < 1 + 2 * (p+1) / (3 * 2 ^ 71) := by
  have hB : (0:ℝ) < 3 ^ (p+1) := by positivity
  have hceil : 3 ^ (p+1) < 2 ^ K :=
    ceiling_lower p _ K x v hstep hK (by positivity) hmin
  have hlow : ((3:ℝ)) ^ (p+1) < 2 ^ K := by exact_mod_cast hceil
  have hnat := seam_gap_at_barina p K x v hstep hK hmin hpX
  have hR : (2:ℝ) ^ K * (3 * 2 ^ 71)
      < 3 ^ (p+1) * (3 * 2 ^ 71) + 3 ^ (p+1) * (2 * (p+1)) := by exact_mod_cast hnat
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]
    have hc : (0:ℝ) < 3 * 2 ^ 71 := by norm_num
    have : (2:ℝ) ^ K < 3 ^ (p+1) * (1 + 2 * (p+1) / (3 * 2 ^ 71)) := by
      rw [mul_add, mul_one, mul_div_assoc]
      rw [← lt_div_iff₀ hc] at *
      nlinarith [hR, hB, hc]
    linarith

/-- **The logarithmic gap.** `0 < K·log 2 − (p+1)·log 3 < 2(p+1)/(3·2^71)`.
    Dividing by `(p+1)·log 2` gives `|log₂3 − K/(p+1)| < δ`, `δ = 2/(3·2^71·ln 2)`,
    the input of Legendre's criterion — which applies for `p+1 ≤ 3.5035·10^10`
    (REQ-MATH-054: within that window all 22 convergent denominators fail). -/
theorem log_gap_at_barina (p K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hmin : ∀ i, 2 ^ 71 ≤ x i)
    (hpX : 2 * p < 3 * 2 ^ 71) :
    0 < (K:ℝ) * Real.log 2 - (p+1) * Real.log 3 ∧
      (K:ℝ) * Real.log 2 - (p+1) * Real.log 3 < 2 * (p+1) / (3 * 2 ^ 71) := by
  obtain ⟨h1, h2⟩ := ratio_bound_at_barina p K x v hstep hK hmin hpX
  have hB : (0:ℝ) < 3 ^ (p+1) := by positivity
  have hApos : (0:ℝ) < 2 ^ K := by positivity
  have hpos : (0:ℝ) < 2 ^ K / 3 ^ (p+1) := div_pos hApos hB
  have hlogeq : Real.log ((2:ℝ) ^ K / 3 ^ (p+1))
      = (K:ℝ) * Real.log 2 - (p+1) * Real.log 3 := by
    rw [Real.log_div (ne_of_gt hApos) (ne_of_gt hB), Real.log_pow, Real.log_pow]
    push_cast
    ring
  constructor
  · rw [← hlogeq]; exact Real.log_pos h1
  · have hle : Real.log ((2:ℝ) ^ K / 3 ^ (p+1)) ≤ (2:ℝ) ^ K / 3 ^ (p+1) - 1 :=
      Real.log_le_sub_one_of_pos hpos
    rw [hlogeq] at hle
    linarith

/-! ### Legendre invocation (March 1-ter)

Feeding `log_gap_at_barina` into Legendre's criterion. The window is stated in **integers**
(`4000·n² ≤ 2079·2⁷¹`, using `ln 2 > 693/1000`) so no irrational appears in the hypothesis;
it is `n ≤ 3.5032·10¹⁰`, within `0.011 %` of the exact window (REQ-MATH-055). -/

/- ============================================================================
   **RETRACTED — commit `da2c8db` (2026-07-25). PERMANENT RECORD, DO NOT REMOVE.**

   CLAIMED: `quotient_is_convergent` (the non-general form, threshold literal `2^71`)
   was kernel-3.

   THE CLAIM WAS FALSE. `lake env lean` printed no `error:` line but had aborted with a
   stack overflow at `maxRecDepth 40000`; at workable recursion depths the proof carried
   `sorryAx`. I read "0 errors" without checking that the compiler had finished.

   REAL OBSTRUCTION: elaboration blow-up on the literal `2^71` inside `nlinarith` — not a
   mathematical gap. The theorem is re-proved below as `quotient_is_convergent_gen`, with
   the threshold abstracted to a variable so no numeral reaches a tactic.

   CONSEQUENCE: the verification protocol is hardened. Every check now tests for `error:`
   AND stack overflow/abort AND `sorryAx` AND presence in the theorem's own
   `#print axioms` probe.

   This block is restored 2026-07-26 after Macindoe's round-10 audit observed, correctly,
   that the standalone note had been superseded at `4856058` by a one-line reference —
   so the record required `git log` to find. A record that requires `git log` is not a
   record. It stays here.
   ============================================================================ -/

/-- `log 2 > 693/1000`, the rational floor used to make the window integral. -/
lemma log_two_gt : (693:ℝ)/1000 < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

/-! ### Legendre invocation, with the threshold ABSTRACT (March 1-ter, second attempt)

The first attempt (commit `da2c8db`, retracted) let the literal `2^71` reach `nlinarith`
and the elaborator blew the stack. Here the threshold is a **variable** `X`; the numeral
appears only when instantiating, never inside a tactic. -/

/-- Logarithmic gap, threshold abstract. Division handled explicitly, no numeral in tactics. -/
theorem log_gap_gen (p X K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hX : 0 < X) (hmin : ∀ i, X ≤ x i)
    (hpX : 2 * p < 3 * X) :
    0 < (K:ℝ) * Real.log 2 - (p+1) * Real.log 3 ∧
      (K:ℝ) * Real.log 2 - (p+1) * Real.log 3 < 2 * ((p:ℝ)+1) / (3 * X) := by
  have hB : (0:ℝ) < 3 ^ (p+1) := by positivity
  have hApos : (0:ℝ) < 2 ^ K := by positivity
  have hXR : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
  have hceil : 3 ^ (p+1) < 2 ^ K :=
    ceiling_lower p _ K x v hstep hK (by positivity) hmin
  have hlow : ((3:ℝ)) ^ (p+1) < 2 ^ K := by exact_mod_cast hceil
  have hcast : (2:ℝ) ^ K * (3 * X) < 3 ^ (p+1) * (3 * X) + 3 ^ (p+1) * (2 * ((p:ℝ)+1)) := by
    have := seam_bound p X K x v hstep hK hX hmin hpX
    have hR : (2:ℝ) ^ K * (3 * X) < 3 ^ (p+1) * (3 * X + 2 * ((p:ℕ)+1)) := by exact_mod_cast this
    push_cast at hR ⊢; linarith
  have h1 : 1 < (2:ℝ) ^ K / 3 ^ (p+1) := by rw [lt_div_iff₀ hB]; linarith
  have hpos : (0:ℝ) < 2 ^ K / 3 ^ (p+1) := div_pos hApos hB
  have hsub : (2:ℝ) ^ K / 3 ^ (p+1) - 1 < 2 * ((p:ℝ)+1) / (3 * X) := by
    rw [div_sub_one (ne_of_gt hB), div_lt_div_iff₀ hB (by positivity)]
    nlinarith [hcast, hB, hXR]
  have hlogeq : Real.log ((2:ℝ) ^ K / 3 ^ (p+1))
      = (K:ℝ) * Real.log 2 - (p+1) * Real.log 3 := by
    rw [Real.log_div (ne_of_gt hApos) (ne_of_gt hB), Real.log_pow, Real.log_pow]
    push_cast; ring
  refine ⟨by rw [← hlogeq]; exact Real.log_pos h1, ?_⟩
  have hle := Real.log_le_sub_one_of_pos hpos
  rw [hlogeq] at hle
  linarith

/-- **THE LEGENDRE STEP, threshold abstract.** Inside the integral window `4000·n² ≤ 2079·X`,
    a surviving cycle above threshold `X` has `K/n` a convergent of `log₂3`.
    Instantiating `X := 2^71` is the Barina case, window `n ≤ 3.5032·10^10` (REQ-MATH-055). -/
theorem quotient_is_convergent_gen (p X K : ℕ) (x v : Fin (p+1) → ℕ)
    (hstep : ∀ i, 3 * x i + 1 = 2 ^ v i * x (i + 1))
    (hK : K = ∑ i, v i) (hX : 0 < X) (hmin : ∀ i, X ≤ x i)
    (hpX : 2 * p < 3 * X)
    (hwin : 4000 * (p+1) ^ 2 ≤ 2079 * X) :
    ∃ m, Rat.divInt (K : ℤ) ((p+1 : ℕ) : ℤ) = (Real.log 3 / Real.log 2).convergent m := by
  obtain ⟨hgap0, hgap⟩ := log_gap_gen p X K x v hstep hK hX hmin hpX
  have hnR : (0:ℝ) < ((p:ℝ)+1) := by positivity
  have hXR : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcastn : (((p+1:ℕ)):ℝ) = (p:ℝ)+1 := by push_cast; ring
  have hsign : Real.log 3 / Real.log 2 - (K:ℝ) / ((p:ℝ)+1) ≤ 0 := by
    rw [div_sub_div _ _ (ne_of_gt hl2) (ne_of_gt hnR)]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [hgap0]
    · positivity
  have hdiff : |Real.log 3 / Real.log 2 - (K:ℝ) / ((p:ℝ)+1)|
      = ((K:ℝ) * Real.log 2 - ((p:ℝ)+1) * Real.log 3) / (((p:ℝ)+1) * Real.log 2) := by
    rw [abs_of_nonpos hsign]; field_simp; ring
  -- the window, step by step (no numeral reaches a tactic in one block)
  have hwinR : (4000:ℝ) * ((p:ℝ)+1) ^ 2 ≤ 2079 * (X:ℝ) := by exact_mod_cast hwin
  have hA : (4:ℝ) * ((p:ℝ)+1) ^ 2 ≤ 2079 * (X:ℝ) / 1000 := by linarith
  have hBn : (2079:ℝ) * (X:ℝ) / 1000 < 3 * (X:ℝ) * Real.log 2 := by
    have hlb := log_two_gt; nlinarith [hlb, hXR]
  have hC : (4:ℝ) * ((p:ℝ)+1) ^ 2 < 3 * (X:ℝ) * Real.log 2 := lt_of_le_of_lt hA hBn
  have hkey : |Real.log 3 / Real.log 2 - (K:ℝ) / ((p:ℝ)+1)| < 1 / (2 * ((p:ℝ)+1) ^ 2) := by
    rw [hdiff, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hmul : ((K:ℝ) * Real.log 2 - ((p:ℝ)+1) * Real.log 3) * (2 * ((p:ℝ)+1) ^ 2)
        ≤ (2 * ((p:ℝ)+1) / (3 * (X:ℝ))) * (2 * ((p:ℝ)+1) ^ 2) :=
      mul_le_mul_of_nonneg_right (le_of_lt hgap) (by positivity)
    have hfin : (2 * ((p:ℝ)+1) / (3 * (X:ℝ))) * (2 * ((p:ℝ)+1) ^ 2)
        < 1 * (((p:ℝ)+1) * Real.log 2) := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [hC, hnR, hl2, hXR]
    linarith
  by_contra hcon
  push_neg at hcon
  have hleg := LegendreApprox.abs_sub_ge_nat_div
      (Real.log 3 / Real.log 2) K (p+1) (by omega) (fun m => hcon m)
  rw [hcastn] at hleg
  linarith [hkey, hleg]

/-! ### The finite discharge (T1, closing step)

Legendre pins `n` to a convergent denominator of `log₂3`. It remains to kill each of the 22
denominators inside the Barina window. Using the classical convergent bound
`θ_j > 1/(q_j + q_{j+1})`, the seam constraint fails at `q_j` as soon as

  `2000 · q_j · (q_j + q_{j+1}) ≤ 2079 · X`,

a purely **integer** inequality — no logarithm, no high precision. Verified for all 22
(REQ-MATH-056; tightest margin 5.17× at `q₂₁ = 6586818670`; the exact test gives 5.44×, so
the integer criterion is conservative as intended). -/

/-- The 22 convergent denominators of `log₂3` below the Barina window, paired with their
    successor (needed for the classical lower bound on `θ_j`). -/
def convPairs : List (ℕ × ℕ) :=
  [(1,1), (1,2), (2,5), (5,12), (12,41), (41,53), (53,306), (306,665), (665,15601),
   (15601,31867), (31867,79335), (79335,111202), (111202,190537), (190537,10590737),
   (10590737,10781274), (10781274,53715833), (53715833,171928773), (171928773,225644606),
   (225644606,397573379), (397573379,6189245291), (6189245291,6586818670),
   (6586818670,65470613321)]

/-- **The finite discharge.** Every convergent denominator in the window fails the seam
    criterion `2000·q·(q+q') ≤ 2079·2^71`. Decided by kernel arithmetic. -/
theorem discharge_all : ∀ qq ∈ convPairs, 2000 * qq.1 * (qq.1 + qq.2) ≤ 2079 * 2 ^ 71 := by
  decide

/-- Sanity: there are exactly 22 of them, and the last is the tightest. -/
theorem convPairs_length : convPairs.length = 22 := by decide

/-- Canary: the tightest case, spelled out — margin 5.17×, and it holds. -/
example : 2000 * 6586818670 * (6586818670 + 65470613321) ≤ 2079 * 2 ^ 71 := by norm_num

/-- Canary (non-vacuity): the criterion is not trivially true — it FAILS one convergent
    beyond the window, which is exactly why the window is where it is. -/
example : ¬ (2000 * 65470613321 * (65470613321 + 137528045312) ≤ 2079 * 2 ^ 71) := by norm_num

#print axioms ceiling_lower
#print axioms ceiling_pinned

#print axioms discharge_all
#print axioms convPairs_length

#print axioms log_gap_gen
#print axioms quotient_is_convergent_gen
#print axioms log_two_gt

#print axioms ratio_bound_at_barina
#print axioms log_gap_at_barina

#print axioms seam_gap_at_barina

#print axioms succ_pow_le_pow_add
#print axioms seam_bound

#print axioms cycle_prod_identity
#print axioms survivor_bound
#print axioms ceiling_upper

end T1Structure
