/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import BernsteinLean.Statement
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Empirical frequencies

For a measurable event `A`, the raw second moment of its indicator is `μ.real A`.
The empirical-mean inequality therefore gives a frequency bound with this probability in the
threshold. The result uses the indicator's raw second moment `p`; its variance is `p(1-p)`.
-/

public section

open MeasureTheory ProbabilityTheory Real
namespace BernsteinLean

/-- The empirical frequency of a measurable event deviates from its probability by more than
`√(2pt/n) + t/(3n)` with probability at most `2 exp(-t)`, where `p = μ.real A`. -/
theorem bernstein_frequency {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {A : Set E} (hA : MeasurableSet A)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => μ)
      {x | √(2 * μ.real A * t / n) + t / (3 * n)
        < |(1 / (n : ℝ)) * ∑ i, A.indicator (1 : E → ℝ) (x i) - μ.real A|}
      ≤ ENNReal.ofReal (2 * exp (-t)) := by
  have hsq : (fun y => A.indicator (1 : E → ℝ) y ^ 2) = A.indicator 1 := by
    funext y
    by_cases hy : y ∈ A <;> simp [hy]
  have h := bernstein_iid_mean μ n hn (A.indicator 1)
    (measurable_one.indicator hA).aemeasurable 1
    (ae_of_all _ fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y)
    (ae_of_all _ fun y => Set.indicator_le_self' (fun _ _ => zero_le_one) y) t ht
  simpa only [hsq, integral_indicator_one hA, one_mul] using h

end BernsteinLean
