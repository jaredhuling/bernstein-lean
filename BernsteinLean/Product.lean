/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Coordinates of a product measure

For probability measures `μ i` on a measurable space `E` and almost-everywhere measurable
functions `f i : E → ℝ`, the random variables `x ↦ f i (x i)` on `ι → E` under `Measure.pi μ`
are independent (mathlib `iIndepFun_pi`), and their integrals, `L²` membership and almost sure
bounds are those of `f i` under `μ i` (the coordinate projection is measure preserving,
`measurePreserving_eval`). These lemmas transport the random-variable forms of Bernstein's
inequality to product-measure forms.
-/

public section

open MeasureTheory ProbabilityTheory

namespace BernsteinLean
namespace Product

variable {ι : Type*} [Fintype ι] {E : Type*} [MeasurableSpace E]
  (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]

/-- Coordinate functions are independent under the product measure. -/
lemma indep {f : ι → E → ℝ} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    iIndepFun (fun i (x : ι → E) => f i (x i)) (Measure.pi μ) :=
  iIndepFun_pi hf

/-- Almost-everywhere measurability transports along a coordinate projection. -/
lemma aemeasurable {f : ι → E → ℝ} (hf : ∀ i, AEMeasurable (f i) (μ i)) (i : ι) :
    AEMeasurable (fun x : ι → E => f i (x i)) (Measure.pi μ) := by
  have h := hf i
  rw [← (measurePreserving_eval μ i).map_eq] at h
  exact h.comp_aemeasurable (measurable_pi_apply i).aemeasurable

/-- Second-moment finiteness transports along a coordinate projection. -/
lemma memLp {f : E → ℝ} {i : ι} (hf : MemLp f 2 (μ i)) :
    MemLp (fun x : ι → E => f (x i)) 2 (Measure.pi μ) :=
  hf.comp_measurePreserving (measurePreserving_eval μ i)

/-- Integrating a coordinate function gives its marginal expectation. -/
lemma integral_eval {g : E → ℝ} {i : ι} (hg : AEStronglyMeasurable g (μ i)) :
    ∫ x, g (x i) ∂(Measure.pi μ) = ∫ y, g y ∂(μ i) := by
  have hg' : AEStronglyMeasurable g (Measure.map (Function.eval i) (Measure.pi μ)) := by
    rw [(measurePreserving_eval μ i).map_eq]; exact hg
  have h := integral_map (μ := Measure.pi μ) (measurable_pi_apply i).aemeasurable hg'
  rw [(measurePreserving_eval μ i).map_eq] at h
  exact h.symm

/-- Almost-sure marginal properties hold for their coordinate functions. -/
lemma ae_eval {p : E → Prop} {i : ι} (h : ∀ᵐ y ∂(μ i), p y) :
    ∀ᵐ x ∂(Measure.pi μ), p (x i) :=
  (measurePreserving_eval μ i).quasiMeasurePreserving.ae h

end Product
end BernsteinLean
