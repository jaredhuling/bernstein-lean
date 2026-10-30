/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import BernsteinLean.MGF
public import BernsteinLean.CGF

/-!
# Tail bounds under the moment conditions of Theorem 2.10

The CGF bound `MGF.cgf_le` and Chernoff's inequality `measure_ge_le_exp_cgf` imply:

* `tail_le_exp`: `P{S ≥ ε} ≤ exp(-λε + vλ²/(2(1 - cλ)))` for `0 < λ`, `cλ < 1`;
* `tail_sqrt`: `P{S ≥ √(2vt) + ct} ≤ e^{-t}` (choose `λ = s/(v + cs)`, `s = √(2vt)`);
* `tail_sqrt_strict`: the same with a strict event and no positivity assumption on `v` or `c`;
* `tail`: `P{S ≥ t} ≤ exp(-t²/(2(v + ct)))` (choose `λ = t/(v + ct)`).

The lemma `sum_ae_eq_zero` treats `v = 0`: under the moment conditions each `Xᵢ` vanishes almost
surely, so `S = 0` almost surely.
-/

public section

open MeasureTheory ProbabilityTheory Real Nat
open scoped ENNReal

namespace BernsteinLean
namespace General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [Fintype ι]

omit [IsProbabilityMeasure P] in
/-- If `Σᵢ E Xᵢ² ≤ 0`, the centered sum vanishes almost surely. -/
lemma sum_ae_eq_zero (X : ι → Ω → ℝ) (hL2 : ∀ i, MemLp (X i) 2 P)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ 0) :
    ∀ᵐ ω ∂P, ∑ i, (X i ω - ∫ ω', X i ω' ∂P) = 0 := by
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ ∫ ω, X i ω ^ 2 ∂P := fun i _ =>
    integral_nonneg fun ω => sq_nonneg (X i ω)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
    (le_antisymm hv (Finset.sum_nonneg hnn))
  have hX : ∀ i, X i =ᵐ[P] 0 := fun i => by
    have h := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X i ω))
      (hL2 i).integrable_sq).1 (hzero i (Finset.mem_univ i))
    filter_upwards [h] with ω hω
    simpa using hω
  have hm : ∀ i, ∫ ω, X i ω ∂P = 0 := fun i => by
    rw [integral_congr_ae (hX i)]; simp
  have hall : ∀ᵐ ω ∂P, ∀ i, X i ω = 0 := ae_all_iff.2 hX
  filter_upwards [hall] with ω hω
  simp [hω, hm]

section MomentConditions

variable (X : ι → Ω → ℝ) (hindep : iIndepFun X P) (hL2 : ∀ i, MemLp (X i) 2 P)
  {v c : ℝ} (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
  (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
  (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
include hindep hL2 hc hv hint hmom

/-- The moment conditions imply exponential integrability and the Bernstein CGF bound. -/
lemma hasBernsteinCGF :
    HasBernsteinCGF (fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) P v c := by
  refine ⟨le_trans (Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => sq_nonneg (X i ω)) hv, hc, ?_⟩
  intro l hl hcl
  exact MGF.cgf_le X hindep hL2 hc hl hcl hv hint hmom

/-- Chernoff's inequality applied with the Bernstein CGF bound. -/
lemma tail_le_exp (ε l : ℝ) (hl : 0 < l) (hcl : c * l < 1) :
    P {ω | ε ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-l * ε + v * l ^ 2 / (2 * (1 - c * l)))) := by
  exact (hasBernsteinCGF X hindep hL2 hc hv hint hmom).tail_le_exp ε l hl hcl

/-- `P{S ≥ √(2vt) + ct} ≤ e^{-t}` when `v > 0` or `c > 0`. -/
lemma tail_sqrt (t : ℝ) (ht : 0 < t) (hvc : 0 < v ∨ 0 < c) :
    P {ω | √(2 * v * t) + c * t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t)) := by
  have hv0 : 0 ≤ v := le_trans (Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => sq_nonneg (X i ω)) hv
  rcases hv0.eq_or_lt with hv0 | hvpos
  · -- v = 0: S = 0 almost surely and the threshold `ct` is positive.
    subst hv0
    have hcpos : 0 < c := hvc.resolve_left (lt_irrefl 0)
    have hS := sum_ae_eq_zero X hL2 hv
    have hnull : P {ω | √(2 * 0 * t) + c * t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hS] with ω hω
      simp only [hω, mul_zero, zero_mul, Real.sqrt_zero, zero_add, not_le]
      positivity
    rw [hnull]; exact bot_le
  · exact (hasBernsteinCGF X hindep hL2 hc hv hint hmom).tail_sqrt hvpos t ht

/-- `P{S > √(2vt) + ct} ≤ e^{-t}`, with no positivity assumption on `v` or `c`. -/
lemma tail_sqrt_strict (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + c * t < ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t)) := by
  have hv0 : 0 ≤ v := le_trans (Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => sq_nonneg (X i ω)) hv
  by_cases hvc : 0 < v ∨ 0 < c
  · refine le_trans (measure_mono ?_) (tail_sqrt X hindep hL2 hc hv hint hmom t ht hvc)
    intro ω hω
    exact le_of_lt (Set.mem_ofPred_eq ▸ hω)
  · push Not at hvc
    have hv' : v = 0 := le_antisymm hvc.1 hv0
    have hc' : c = 0 := le_antisymm hvc.2 hc
    subst hv' hc'
    have hS := sum_ae_eq_zero X hL2 hv
    have hnull : P {ω | √(2 * 0 * t) + 0 * t < ∑ i, (X i ω - ∫ ω', X i ω' ∂P)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hS] with ω hω
      simp [hω]
    rw [hnull]; exact bot_le

/-- **Corollary 2.11**: `P{S ≥ t} ≤ exp(-t²/(2(v + ct)))` for `t > 0`. -/
lemma tail (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + c * t))))) := by
  have hv0 : 0 ≤ v := le_trans (Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => sq_nonneg (X i ω)) hv
  rcases hv0.eq_or_lt with hv0 | hvpos
  · subst hv0
    have hS := sum_ae_eq_zero X hL2 hv
    have hnull : P {ω | t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hS] with ω hω
      simp only [hω, not_le]
      exact ht
    rw [hnull]; exact bot_le
  · exact (hasBernsteinCGF X hindep hL2 hc hv hint hmom).tail hvpos t ht

end MomentConditions

end General
end BernsteinLean
