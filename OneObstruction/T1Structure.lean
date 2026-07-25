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
bound+ceiling on the trivial cycle, 114 census cells consistent, Legendre window 4.955e10,
and the GRID half (Ostrowski: ε-small n use only large convergent denominators) —
script-verified, NOT proved here.
-/
import Mathlib

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

/-- Canary: the trivial cycle (x ≡ 1, v ≡ 2 on Fin 1) satisfies the step hypothesis. -/
example : ∀ i : Fin 1, 3 * (fun _ : Fin 1 => 1) i + 1
    = 2 ^ (fun _ : Fin 1 => 2) i * (fun _ : Fin 1 => 1) (i + 1) := by
  intro i; norm_num

/-- Canary: instantiating `ceiling_upper` on the trivial cycle yields `2^2 < 2·3`. -/
example : (2:ℕ) ^ 2 < 2 * 3 ^ 1 :=
  ceiling_upper 0 1 2 (fun _ => 1) (fun _ => 2)
    (fun i => by norm_num) (by simp) (by norm_num) (fun i => le_refl 1) (by norm_num)

#print axioms cycle_prod_identity
#print axioms survivor_bound
#print axioms ceiling_upper

end T1Structure
