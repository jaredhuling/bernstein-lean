/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import BernsteinLean.Statement

/-!
# Examples of Bernstein's inequality

These examples apply the library results to indicators and bounded coordinates, and examine
empty families and the positivity assumptions for non-strict tail events.
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace BernsteinLean.Examples

/-- The i.i.d. form applied to the indicator of a measurable set `A` (`0 ≤ 1_A ≤ 1`): the
empirical frequency of `A` among `n` draws deviates from `μ A` by more than
`√(2 (∫ 1_A²) t/n) + t/(3n)` with probability at most `2e^{-t}`. -/
theorem indicator_moment_bound {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    {A : Set E} (hA : MeasurableSet A) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => μ)
        {x | √(2 * (∫ y, A.indicator (1 : E → ℝ) y ^ 2 ∂μ) * t / n) + 1 * t / (3 * n)
          < |(1 / (n : ℝ)) * ∑ i, A.indicator (1 : E → ℝ) (x i) - ∫ y, A.indicator 1 y ∂μ|}
      ≤ ENNReal.ofReal (2 * exp (-t)) :=
  bernstein_iid_mean μ n hn (A.indicator 1) (measurable_one.indicator hA).aemeasurable 1
    (ae_of_all _ fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y)
    (ae_of_all _ fun y => Set.indicator_le_self' (fun _ _ => zero_le_one) y) t ht

/-- The bounded one-sided form for coordinates of a product of probability measures on `ℝ`
supported in `(-∞, 1]`, with `v` any upper bound on the sum of second moments. -/
theorem bounded_coordinates {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hL2 : ∀ i, MemLp id 2 (μ i)) (h1 : ∀ i, ∀ᵐ y ∂(μ i), y ≤ 1) (v : ℝ)
    (hv : ∑ i, ∫ y, y ^ 2 ∂(μ i) ≤ v) (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ ∑ i, (x i - ∫ y, y ∂(μ i))}
      ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + 1 * t / 3))))) :=
  bernstein_bounded_tail_pi μ (fun _ => id) hL2 1 v zero_le_one h1 hv t ht

/-- The general CGF bound with `c = b/3`, using the moment conditions established by
`Bounded.integrable_max_pow` and `Bounded.moment_condition`. -/
theorem bounded_cgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (b v : ℝ) (hb : 0 ≤ b) (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ b)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (l : ℝ) (hl : 0 < l) (hbl : b / 3 * l < 1) :
    cgf (fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) P l ≤ v * l ^ 2 / (2 * (1 - b / 3 * l)) :=
  bernstein_cgf X hindep hL2 v (b / 3) (by positivity) hv
    (Bounded.integrable_max_pow X hL2 hb hXb) (Bounded.moment_condition X hL2 hb hXb hv) l hl hbl

/-- Empty index type: the centered sum is `0`, and the strict tail form applies with `v = 0`
and `c = 0`, where the non-strict form would be false. -/
theorem empty_strict_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Empty → Ω → ℝ) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * 0 * t) + 0 * t < ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t)) :=
  bernstein_tail_sqrt_strict X (iIndepFun.of_subsingleton) (fun i => i.elim) 0 0 le_rfl
    (by simp) (fun i => i.elim) (fun q _ => by simp) t ht

/-- For an empty family with `v = c = 0`, the event `{S ≥ 0}` has probability
`1 > e^{-1}`. This establishes the need for `0 < v ∨ 0 < c` in `bernstein_tail_sqrt`. -/
theorem zero_closed_counterexample {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Empty → Ω → ℝ) :
    ¬ P {ω | √(2 * 0 * 1) + 0 * 1 ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-1)) := by
  simp only [mul_zero, zero_mul, Real.sqrt_zero, add_zero, Finset.univ_eq_empty,
    Finset.sum_empty, le_refl, Set.ofPred_true, measure_univ, not_le]
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by
    rw [Real.exp_lt_one_iff]; norm_num)

end BernsteinLean.Examples
