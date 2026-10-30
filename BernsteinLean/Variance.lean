/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import BernsteinLean.Statement
public import Mathlib.Probability.Moments.Variance

/-! # Bernstein bounds in terms of variances

The bounded theorem applies to the centered variables `Xᵢ - E Xᵢ`, whose second moments
are their variances. These results assume a bound on the centered summands and an upper bound
on the sum of their variances.
-/

public section

open MeasureTheory ProbabilityTheory Real
namespace BernsteinLean

/-- Bernstein's upper-tail bound using the sum of variances and a bound on centered summands. -/
theorem bernstein_variance_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hind : iIndepFun X P) (hL2 : ∀ i, MemLp (X i) 2 P) (b v : ℝ) (hb : 0 ≤ b)
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω - ∫ ω', X i ω' ∂P ≤ b)
    (hv : ∑ i, variance (X i) P ≤ v) (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
  have hm : ∀ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂P) ∂P = 0 := by
    intro i
    rw [integral_sub ((hL2 i).integrable one_le_two) (integrable_const _)]
    simp
  have hv' : ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂P) ^ 2 ∂P ≤ v := by
    simpa only [variance_eq_integral (hL2 _).aemeasurable] using hv
  have h := bernstein_bounded_tail
    (fun i ω => X i ω - ∫ ω', X i ω' ∂P)
    (hind.comp (fun i x => x - ∫ ω', X i ω' ∂P) (fun _ => measurable_id.sub_const _))
    (fun i => (hL2 i).sub (memLp_const _)) b v hb hX hv' t ht
  simpa only [hm, sub_zero] using h


/-- The strict two-sided square-root bound using variances and absolute bounds after centering. -/
theorem bernstein_variance_two_sided_sqrt_strict {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hind : iIndepFun X P) (hL2 : ∀ i, MemLp (X i) 2 P) (b v : ℝ) (hb : 0 ≤ b)
    (hX : ∀ i, ∀ᵐ ω ∂P, |X i ω - ∫ ω', X i ω' ∂P| ≤ b)
    (hv : ∑ i, variance (X i) P ≤ v) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + b * t / 3 < |∑ i, (X i ω - ∫ ω', X i ω' ∂P)|}
      ≤ ENNReal.ofReal (2 * exp (-t)) := by
  have hm : ∀ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂P) ∂P = 0 := by
    intro i
    rw [integral_sub ((hL2 i).integrable one_le_two) (integrable_const _)]
    simp
  have hv' : ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂P) ^ 2 ∂P ≤ v := by
    simpa only [variance_eq_integral (hL2 _).aemeasurable] using hv
  have h := bernstein_bounded_two_sided_sqrt_strict
    (fun i ω => X i ω - ∫ ω', X i ω' ∂P)
    (hind.comp (fun i x => x - ∫ ω', X i ω' ∂P) (fun _ => measurable_id.sub_const _))
    (fun i => ((hL2 i).sub (memLp_const _)).aemeasurable) b v hb hX hv' t ht
  simpa only [hm, sub_zero] using h


end BernsteinLean
