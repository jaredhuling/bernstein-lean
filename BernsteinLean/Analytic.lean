/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Elementary real inequalities for Bernstein's inequality

* `exp_le_quadratic_of_nonpos`: `eᵘ ≤ 1 + u + u²/2` for `u ≤ 0`, that is `φ(u) ≤ u²/2` with
  `φ(u) = eᵘ - u - 1` (Boucheron, Lugosi and Massart 2013, proof of Theorem 2.10).
* `hasSum_exp_tail`: `Σ_{k ≥ 0} x^(k+3)/(k+3)! = eˣ - 1 - x - x²/2`.
* `exp_le_series_bound`: `eˣ ≤ 1 + x + x²/2 + Σ_{k ≥ 0} (x₊)^(k+3)/(k+3)!` for every real `x`.
* `two_mul_three_pow_le_factorial`: `2 · 3^(q-2) ≤ q!` for `q ≥ 2`.
-/

public section

open Real Nat

namespace BernsteinLean
namespace Analytic

/-- `eᵘ ≤ 1 + u + u²/2` for `u ≤ 0`. -/
lemma exp_le_quadratic_of_nonpos {u : ℝ} (hu : u ≤ 0) : exp u ≤ 1 + u + u ^ 2 / 2 := by
  -- h(w) = e^w (1 - w + w²/2) is monotone since h'(w) = e^w w²/2 ≥ 0, and h(0) = 1.
  set h : ℝ → ℝ := fun w => exp w * (1 - w + w ^ 2 / 2) with hh
  have hd : ∀ w, HasDerivAt h (exp w * (w ^ 2 / 2)) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ => 1 - w + w ^ 2 / 2) (-1 + (2 * w) / 2) w := by
      have := ((hasDerivAt_id w).const_sub 1).add ((hasDerivAt_pow 2 w).div_const 2)
      convert this using 1
      · ext x; simp
      · norm_num
    convert (Real.hasDerivAt_exp w).mul h1 using 1
    ring
  have hmono : Monotone h := by
    refine monotone_of_deriv_nonneg (fun w => (hd w).differentiableAt) (fun w => ?_)
    rw [(hd w).deriv]
    positivity
  have hpos : 0 < 1 + u + u ^ 2 / 2 := by nlinarith [sq_nonneg (u + 1)]
  have h0 : h 0 = 1 := by simp [hh]
  have key : 1 ≤ h (-u) := h0 ▸ hmono (by linarith)
  simp only [hh] at key
  have : exp (-u) * exp u = 1 := by rw [← Real.exp_add]; simp
  have e : exp u = exp u * 1 := by ring
  rw [e]
  calc exp u * 1 ≤ exp u * (exp (-u) * (1 - -u + (-u) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left key (exp_pos u).le
    _ = (exp (-u) * exp u) * (1 + u + u ^ 2 / 2) := by ring
    _ = 1 + u + u ^ 2 / 2 := by rw [this, one_mul]

/-- The tail of the exponential series after the quadratic term. -/
lemma hasSum_exp_tail (x : ℝ) :
    HasSum (fun k : ℕ => x ^ (k + 3) / ((k + 3)! : ℝ)) (exp x - 1 - x - x ^ 2 / 2) := by
  have hs : HasSum (fun n : ℕ => x ^ n / (n ! : ℝ)) (exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have := (hasSum_nat_add_iff' 3).2 hs
  convert this using 1
  simp [Finset.sum_range_succ]
  ring

/-- `eˣ ≤ 1 + x + x²/2 + Σ_{k ≥ 0} (max x 0)^(k+3)/(k+3)!` for every real `x`. -/
lemma exp_le_series_bound (x : ℝ) :
    exp x ≤ 1 + x + x ^ 2 / 2 + ∑' k : ℕ, (max x 0) ^ (k + 3) / ((k + 3)! : ℝ) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [max_eq_right hx]
    simp only [ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, not_false_eq_true,
      zero_pow, zero_div, tsum_zero, add_zero]
    exact exp_le_quadratic_of_nonpos hx
  · rw [max_eq_left hx.le, (hasSum_exp_tail x).tsum_eq]
    linarith

/-- `2 · 3^k ≤ (k+2)!`. -/
lemma two_mul_three_pow_le_factorial (k : ℕ) : 2 * 3 ^ k ≤ (k + 2)! := by
  induction k with
  | zero => simp [Nat.factorial]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

end Analytic
end BernsteinLean
