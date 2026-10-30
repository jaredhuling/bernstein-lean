/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import Mathlib.Probability.Moments.Basic

/-!
# One-sided Bernstein cumulant generating function bounds

`HasBernsteinCGF S P v c` requires nonnegative `v` and `c`, together with exponential
integrability and the CGF bound for each `λ > 0` satisfying `cλ < 1`. The predicate is stated
without a centering hypothesis. The theorem `General.hasBernsteinCGF` establishes it for the
centered sum under the moment conditions.

The methods `tail_sqrt` and `tail` require `v > 0`. The moment-condition theorems in `General`
also cover `v = 0`, using the resulting almost-sure equality of each summand to zero.
-/

public section

open MeasureTheory ProbabilityTheory Real
namespace BernsteinLean

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A one-sided sub-gamma CGF bound with the integrability required for Chernoff's inequality.
The positive exponential parameter satisfies `cλ < 1`. -/
@[expose] def HasBernsteinCGF (S : Ω → ℝ) (P : Measure Ω) (v c : ℝ) : Prop :=
  0 ≤ v ∧ 0 ≤ c ∧ ∀ l : ℝ, 0 < l → c * l < 1 →
    Integrable (fun ω => exp (l * S ω)) P ∧ cgf S P l ≤ v * l ^ 2 / (2 * (1 - c * l))

namespace HasBernsteinCGF

variable [IsProbabilityMeasure P] {S : Ω → ℝ} {v c : ℝ}

/-- Chernoff's inequality for each `l > 0` satisfying `c * l < 1`. -/
lemma tail_le_exp (h : HasBernsteinCGF S P v c) (ε l : ℝ)
    (hl : 0 < l) (hcl : c * l < 1) :
    P {ω | ε ≤ S ω}
      ≤ ENNReal.ofReal (exp (-l * ε + v * l ^ 2 / (2 * (1 - c * l)))) := by
  obtain ⟨hexp, hcgf⟩ := h.2.2 l hl hcl
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (measure_ge_le_exp_cgf ε hl.le hexp).trans ?_
  gcongr

/-- The square-root tail bound under the CGF condition and `v > 0`. -/
lemma tail_sqrt (h : HasBernsteinCGF S P v c) (hv : 0 < v) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + c * t ≤ S ω} ≤ ENNReal.ofReal (exp (-t)) := by
  have hc := h.2.1
  set s := √(2 * v * t) with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 2 * v * t := Real.sq_sqrt (by positivity)
  have hD : 0 < v + c * s := by positivity
  set l := s / (v + c * s) with hl_def
  have hl : 0 < l := div_pos hs0 hD
  have hcl : c * l < 1 := by
    rw [hl_def, mul_div_assoc', div_lt_one hD]; linarith
  refine (h.tail_le_exp _ l hl hcl).trans ?_
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  congr 1
  have h1 : 1 - c * (s / (v + c * s)) = v / (v + c * s) := by field_simp; ring
  rw [hl_def, h1]
  field_simp
  linear_combination (-1 : ℝ) * hs2

/-- The rational tail bound obtained at `t / (v + c * t)` when `v > 0`. -/
lemma tail (h : HasBernsteinCGF S P v c) (hv : 0 < v) (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ S ω} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + c * t))))) := by
  have hc := h.2.1
  have hD : 0 < v + c * t := by positivity
  set l := t / (v + c * t) with hl_def
  have hl : 0 < l := div_pos ht hD
  have hcl : c * l < 1 := by
    rw [hl_def, mul_div_assoc', div_lt_one hD]; linarith
  refine (h.tail_le_exp _ l hl hcl).trans ?_
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  congr 1
  have h1 : 1 - c * (t / (v + c * t)) = v / (v + c * t) := by field_simp; ring
  rw [hl_def, h1]
  field_simp
  ring

end HasBernsteinCGF
end BernsteinLean
