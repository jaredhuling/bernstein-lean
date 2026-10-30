/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import BernsteinLean

/-! # Degenerate cases and necessary hypotheses -/

public section

open MeasureTheory ProbabilityTheory Real
namespace BernsteinLean.BoundaryTests

/-- For zero summands, the tail probability at a positive threshold is zero. -/
theorem zero_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (t : ℝ) (ht : 0 < t) :
    P {_ω | t ≤ |∑ _i : ι, ((0 : ℝ) - ∫ _ω' : Ω, (0 : ℝ) ∂P)|} = 0 := by
  simp [not_le.mpr ht]

/-- The strict empirical-mean theorem applies when the function and its upper bound are zero. -/
theorem zero_mean {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => μ)
      {_x | √(2 * (∫ _y : E, (0 : ℝ)^2 ∂μ) * t / n) + 0 * t / (3 * n)
        < |(1 / (n : ℝ)) * ∑ _i : Fin n, (0 : ℝ) - ∫ _y : E, (0 : ℝ) ∂μ|}
      ≤ ENNReal.ofReal (2 * exp (-t)) :=
  BernsteinLean.bernstein_iid_mean μ n hn (fun _ => 0) aemeasurable_const 0
    (ae_of_all _ fun _ => le_rfl) (ae_of_all _ fun _ => le_rfl) t ht

/-- The constant function 1 gives a counterexample to the empirical-mean bound at `n = 0`. -/
theorem zero_sample_counterexample {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] :
    ¬ Measure.pi (fun _ : Fin 0 => μ)
      {_x | √(2 * (∫ _y : E, (1 : ℝ)^2 ∂μ) * 2 / (0 : ℝ))
          + 1 * 2 / (3 * (0 : ℝ))
        < |(1 / (0 : ℝ)) * ∑ _i : Fin 0, (1 : ℝ) - ∫ _y : E, (1 : ℝ) ∂μ|}
      ≤ ENNReal.ofReal (2 * exp (-2)) := by
  have he : 2 * exp (-2) < 1 := by
    have h : 2 < exp (2 : ℝ) := by linarith [Real.add_one_le_exp (2 : ℝ)]
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    exact h
  have hh : ENNReal.ofReal (2 * exp (-2)) < 1 := by
    simpa using (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 he
  simpa using hh


/-- The CGF bound at `c = 0` applies to nonpositive L² variables without a lower bound. -/
theorem zero_scale_cgf {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hind : iIndepFun X P) (hL2 : ∀ i, MemLp (X i) 2 P)
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 0) (v : ℝ)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (l : ℝ) (hl : 0 < l) :
    cgf (fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) P l ≤ v * l ^ 2 / 2 := by
  have h := BernsteinLean.bernstein_cgf X hind hL2 v (0 / 3) (by norm_num) hv
    (BernsteinLean.Bounded.integrable_max_pow X hL2 (b := 0) le_rfl hX)
    (BernsteinLean.Bounded.moment_condition X hL2 (b := 0) le_rfl hX hv) l hl (by norm_num)
  simpa using h

end BernsteinLean.BoundaryTests
