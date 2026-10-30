/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import BernsteinLean.General

/-!
# Bernstein bounds for summands bounded above

For summands with finite second moments and `Xᵢ ≤ b` almost surely, where `b ≥ 0`, the
moment conditions of Theorem 2.10 hold with `v = Σᵢ E Xᵢ²` and `c = b/3`. This is the bounded case
in the remark after Corollary 2.11 of Boucheron, Lugosi and Massart (2013). The statements
here permit any upper bound `v` on `Σᵢ E Xᵢ²`.

* `max_pow_le`: `(x₊)^q ≤ b^(q-2) x²` for `x ≤ b`, `b ≥ 0`, `q ≥ 2`;
* `pow_le_factorial_mul`: `b^(q-2) ≤ q! (b/3)^(q-2) / 2` for `b ≥ 0`, `q ≥ 2`
  (equivalently `2 · 3^(q-2) ≤ q!`);
* `integrable_max_pow`, `moment_condition`: the hypotheses of Theorem 2.10 with `c = b/3`.
-/

public section

open MeasureTheory ProbabilityTheory Real Nat
open scoped ENNReal

namespace BernsteinLean
namespace Bounded

lemma max_pow_le {x b : ℝ} (hb : 0 ≤ b) (hx : x ≤ b) {q : ℕ} (hq : 2 ≤ q) :
    max x 0 ^ q ≤ b ^ (q - 2) * x ^ 2 := by
  rcases le_or_gt x 0 with h | h
  · rw [max_eq_right h, zero_pow (by omega)]
    positivity
  · rw [max_eq_left h.le]
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
    rw [show k + 2 - 2 = k by omega, pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.le hx k) (sq_nonneg x)

lemma pow_le_factorial_mul {b : ℝ} (hb : 0 ≤ b) {q : ℕ} (hq : 2 ≤ q) :
    b ^ (q - 2) ≤ q ! * (b / 3) ^ (q - 2) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  rw [show k + 2 - 2 = k by omega, div_pow]
  have h : (2 * 3 ^ k : ℝ) ≤ ((k + 2)! : ℝ) := by
    exact_mod_cast Analytic.two_mul_three_pow_le_factorial k
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have hbk : 0 ≤ b ^ k := pow_nonneg hb k
  rw [le_div_iff₀ two_pos, mul_div_assoc', le_div_iff₀ h3]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [Fintype ι]

omit [IsProbabilityMeasure P] [Fintype ι] in
lemma integrable_max_pow (X : ι → Ω → ℝ) (hL2 : ∀ i, MemLp (X i) 2 P) {b : ℝ} (hb : 0 ≤ b)
    (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ b) :
    ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P := by
  intro i q hq
  have hm : AEStronglyMeasurable (fun ω => max (X i ω) 0 ^ q) P :=
    (((hL2 i).aestronglyMeasurable.aemeasurable.max aemeasurable_const).pow_const q
      ).aestronglyMeasurable
  refine ((hL2 i).integrable_sq.const_mul (b ^ (q - 2))).mono' hm ?_
  filter_upwards [hXb i] with ω hω
  rw [Real.norm_of_nonneg (pow_nonneg (le_max_right _ _) _)]
  exact max_pow_le hb hω (by omega)

omit [IsProbabilityMeasure P] in
lemma moment_condition (X : ι → Ω → ℝ) (hL2 : ∀ i, MemLp (X i) 2 P) {b v : ℝ} (hb : 0 ≤ b)
    (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ b) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) :
    ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * (b / 3) ^ (q - 2) / 2 := by
  intro q hq
  have hv0 : 0 ≤ v := le_trans (Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => sq_nonneg (X i ω)) hv
  calc ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ ∑ i, b ^ (q - 2) * ∫ ω, X i ω ^ 2 ∂P := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← integral_const_mul]
        refine integral_mono_ae (integrable_max_pow X hL2 hb hXb i q hq)
          ((hL2 i).integrable_sq.const_mul _) ?_
        filter_upwards [hXb i] with ω hω
        exact max_pow_le hb hω (by omega)
    _ = b ^ (q - 2) * ∑ i, ∫ ω, X i ω ^ 2 ∂P := by rw [Finset.mul_sum]
    _ ≤ b ^ (q - 2) * v := mul_le_mul_of_nonneg_left hv (pow_nonneg hb _)
    _ ≤ q ! * (b / 3) ^ (q - 2) / 2 * v :=
        mul_le_mul_of_nonneg_right (pow_le_factorial_mul hb (by omega)) hv0
    _ = q ! * v * (b / 3) ^ (q - 2) / 2 := by ring

end Bounded
end BernsteinLean
