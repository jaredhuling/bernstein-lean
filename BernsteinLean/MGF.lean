/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import BernsteinLean.Analytic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The cumulant generating function bound of Bernstein's inequality

This module proves the CGF bound in Boucheron, Lugosi and Massart (2013),
Theorem 2.10.

* `single`: for one random variable `Y ∈ L²` with integrable positive-part moments, `λ ≥ 0`,
  and a summable weighted moment series (the premise `hsum` below),
  `e^{λY}` is integrable and
  `E e^{λY} ≤ 1 + λ E Y + λ²/2 · E Y² + Σ_{k ≥ 0} λ^(k+3) E (Y₊)^(k+3)/(k+3)!`.
  The interchange of expectation and series (the book's monotone convergence step) is
  `integral_tsum_of_summable_integral_norm`; integrability of the series is proved through
  `lintegral_tsum`.
* `integrable_exp_mul_sum₀`: integrability of `exp (λ Σ Yᵢ)` for independent, almost everywhere
  measurable `Yᵢ`, assuming each `exp (λ Yᵢ)` is integrable.
* `cgf_le`: for independent `Xᵢ` satisfying the moment conditions of Theorem 2.10 and
  `0 < λ`, `cλ < 1`, the centered sum `S = Σ (Xᵢ - E Xᵢ)` has integrable `e^{λS}` and
  `ψ_S(λ) ≤ vλ²/(2(1 - cλ))`.
-/

public section

open MeasureTheory ProbabilityTheory Real Nat
open scoped ENNReal

namespace BernsteinLean
namespace MGF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Per-summand bound: the exponential moment is controlled by the first two moments and the
summable series of positive-part moments. Finite moments alone are insufficient. -/
lemma single (Y : Ω → ℝ) (hY : MemLp Y 2 P) {l : ℝ} (hl : 0 ≤ l)
    (hint : ∀ k : ℕ, Integrable (fun ω => max (Y ω) 0 ^ (k + 3)) P)
    (hsum : Summable
      (fun k : ℕ => l ^ (k + 3) * (∫ ω, max (Y ω) 0 ^ (k + 3) ∂P) / ((k + 3)! : ℝ))) :
    Integrable (fun ω => exp (l * Y ω)) P ∧
    ∫ ω, exp (l * Y ω) ∂P ≤ 1 + l * ∫ ω, Y ω ∂P + l ^ 2 / 2 * ∫ ω, Y ω ^ 2 ∂P
      + ∑' k : ℕ, l ^ (k + 3) * (∫ ω, max (Y ω) 0 ^ (k + 3) ∂P) / ((k + 3)! : ℝ) := by
  set g : ℕ → Ω → ℝ := fun k ω => (max (l * Y ω) 0) ^ (k + 3) / ((k + 3)! : ℝ) with hg_def
  have hmax : ∀ ω, max (l * Y ω) 0 = l * max (Y ω) 0 := fun ω => by
    rw [mul_max_of_nonneg _ _ hl, mul_zero]
  have hg : ∀ k, g k = fun ω => l ^ (k + 3) / ((k + 3)! : ℝ) * max (Y ω) 0 ^ (k + 3) := by
    intro k; funext ω; simp only [g, hmax, mul_pow]; ring
  have hg_int : ∀ k, Integrable (g k) P := fun k => by
    rw [hg]; exact (hint k).const_mul _
  have hg_nonneg : ∀ k ω, 0 ≤ g k ω := fun k ω => by
    simp only [g]; exact div_nonneg (pow_nonneg (le_max_right _ _) _) (by positivity)
  have hg_integral : ∀ k, ∫ ω, g k ω ∂P
      = l ^ (k + 3) * (∫ ω, max (Y ω) 0 ^ (k + 3) ∂P) / ((k + 3)! : ℝ) := by
    intro k; rw [hg, integral_const_mul]; ring
  have hnorm : ∀ k, ∫ ω, ‖g k ω‖ ∂P = ∫ ω, g k ω ∂P := fun k => by
    congr 1; funext ω; exact Real.norm_of_nonneg (hg_nonneg k ω)
  have hsum' : Summable fun k => ∫ ω, ‖g k ω‖ ∂P := by
    simp_rw [hnorm, hg_integral]; exact hsum
  have hsumg : Summable fun k => ∫ ω, g k ω ∂P := by
    have h := hsum'; simp_rw [hnorm] at h; exact h
  set G : Ω → ℝ := fun ω => ∑' k, g k ω with hG_def
  have hG : G = fun ω => exp (max (l * Y ω) 0) - 1 - max (l * Y ω) 0
      - (max (l * Y ω) 0) ^ 2 / 2 := funext fun ω => (Analytic.hasSum_exp_tail _).tsum_eq
  have hYm : AEMeasurable Y P := hY.aestronglyMeasurable.aemeasurable
  have hG_meas : AEStronglyMeasurable G P := by
    rw [hG]
    have h1 : AEMeasurable (fun ω => max (l * Y ω) 0) P := (hYm.const_mul l).max aemeasurable_const
    exact ((((h1.exp).sub aemeasurable_const).sub h1).sub
      ((h1.pow_const 2).div_const 2)).aestronglyMeasurable
  have hG_nonneg : ∀ ω, 0 ≤ G ω := fun ω => tsum_nonneg fun k => hg_nonneg k ω
  have hG_int : Integrable G P := by
    refine ⟨hG_meas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hG_nonneg)]
    have h1 : ∀ ω, ENNReal.ofReal (G ω) = ∑' k, ENNReal.ofReal (g k ω) := fun ω =>
      ENNReal.ofReal_tsum_of_nonneg (fun k => hg_nonneg k ω) (Analytic.hasSum_exp_tail _).summable
    simp_rw [h1]
    rw [lintegral_tsum (fun k => (hg_int k).aemeasurable.ennreal_ofReal)]
    have h2 : ∀ k, ∫⁻ ω, ENNReal.ofReal (g k ω) ∂P = ENNReal.ofReal (∫ ω, g k ω ∂P) := fun k =>
      (ofReal_integral_eq_lintegral_ofReal (hg_int k) (ae_of_all _ (hg_nonneg k))).symm
    simp_rw [h2]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg (hg_nonneg k)) hsumg]
    exact ENNReal.ofReal_lt_top
  have hGint_eq : ∫ ω, G ω ∂P = ∑' k, ∫ ω, g k ω ∂P :=
    (integral_tsum_of_summable_integral_norm hg_int hsum').symm
  have hpt : ∀ ω, exp (l * Y ω) ≤ 1 + l * Y ω + l ^ 2 / 2 * Y ω ^ 2 + G ω := fun ω => by
    have := Analytic.exp_le_series_bound (l * Y ω)
    simp only [hG_def, hg_def]
    calc exp (l * Y ω) ≤ _ := this
      _ = _ := by ring
  have hY1 : Integrable Y P := hY.integrable one_le_two
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := hY.integrable_sq
  have hB : Integrable (fun ω => 1 + l * Y ω + l ^ 2 / 2 * Y ω ^ 2 + G ω) P :=
    (((integrable_const 1).add (hY1.const_mul l)).add (hY2.const_mul _)).add hG_int
  have hexp_meas : AEStronglyMeasurable (fun ω => exp (l * Y ω)) P :=
    (hYm.const_mul l).exp.aestronglyMeasurable
  have hexp : Integrable (fun ω => exp (l * Y ω)) P :=
    hB.mono' hexp_meas (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (exp_pos _).le]; exact hpt ω)
  refine ⟨hexp, ?_⟩
  calc ∫ ω, exp (l * Y ω) ∂P ≤ ∫ ω, (1 + l * Y ω + l ^ 2 / 2 * Y ω ^ 2 + G ω) ∂P :=
        integral_mono hexp hB hpt
    _ = 1 + l * ∫ ω, Y ω ∂P + l ^ 2 / 2 * ∫ ω, Y ω ^ 2 ∂P + ∫ ω, G ω ∂P := by
        have hA : Integrable (fun ω => 1 + l * Y ω) P := (integrable_const 1).add (hY1.const_mul l)
        have hA2 : Integrable (fun ω => 1 + l * Y ω + l ^ 2 / 2 * Y ω ^ 2) P :=
          hA.add (hY2.const_mul _)
        rw [integral_add (f := fun ω => 1 + l * Y ω + l ^ 2 / 2 * Y ω ^ 2) hA2 hG_int,
          integral_add (f := fun ω => 1 + l * Y ω) hA (hY2.const_mul _),
          integral_add (f := fun _ => (1 : ℝ)) (integrable_const 1) (hY1.const_mul l),
          integral_const_mul, integral_const_mul]
        simp
    _ = _ := by rw [hGint_eq]; simp_rw [hg_integral]

variable {ι : Type*}

/-- Integrability of `exp (λ Σᵢ Yᵢ)` for independent, almost everywhere measurable `Yᵢ`,
assuming integrability of every coordinate exponential `exp (λ Yᵢ)`. -/
lemma integrable_exp_mul_sum₀ {Y : ι → Ω → ℝ} (hindep : iIndepFun Y P)
    (hmeas : ∀ i, AEMeasurable (Y i) P) {l : ℝ}
    (hint : ∀ i, Integrable (fun ω => exp (l * Y i ω)) P) (s : Finset ι) :
    Integrable (fun ω => exp (l * (∑ i ∈ s, Y i) ω)) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi h_rec =>
    rw [Finset.sum_insert hi]
    have hind : Y i ⟂ᵢ[P] (∑ j ∈ s, Y j) :=
      (hindep.indepFun_finsetSum_of_notMem₀ hmeas hi).symm
    exact IndepFun.integrable_exp_mul_add hind (hint i) h_rec

variable [Fintype ι]

/-- **CGF bound** (Boucheron, Lugosi and Massart 2013, Theorem 2.10, first display), together
with integrability of `e^{λS}`, so `ψ_S(λ)` is the logarithm of a finite, positive exponential
moment. -/
theorem cgf_le (X : ι → Ω → ℝ) (hindep : iIndepFun X P) (hL2 : ∀ i, MemLp (X i) 2 P)
    {v c l : ℝ} (hc : 0 ≤ c) (hl : 0 < l) (hcl : c * l < 1)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2) :
    Integrable (fun ω => exp (l * ∑ i, (X i ω - ∫ ω', X i ω' ∂P))) P ∧
    cgf (fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) P l ≤ v * l ^ 2 / (2 * (1 - c * l)) := by
  classical
  set m : ι → ℝ := fun i => ∫ ω, X i ω ∂P with hm
  have hr0 : 0 ≤ c * l := mul_nonneg hc hl.le
  have hv0 : 0 ≤ v := le_trans (Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => sq_nonneg (X i ω)) hv
  set a : ι → ℕ → ℝ := fun i k =>
    l ^ (k + 3) * (∫ ω, max (X i ω) 0 ^ (k + 3) ∂P) / ((k + 3)! : ℝ) with ha
  set b : ℕ → ℝ := fun k => v * l ^ 2 / 2 * (c * l) * (c * l) ^ k with hb
  have ha0 : ∀ i k, 0 ≤ a i k := fun i k => by
    simp only [a]
    exact div_nonneg (mul_nonneg (pow_nonneg hl.le _)
      (integral_nonneg fun ω => pow_nonneg (le_max_right _ _) _)) (by positivity)
  have hsum_ab : ∀ k, ∑ i, a i k ≤ b k := fun k => by
    have hq := hmom (k + 3) (by omega)
    rw [show k + 3 - 2 = k + 1 by omega] at hq
    have hf : (0 : ℝ) < ((k + 3)! : ℝ) := by positivity
    calc ∑ i, a i k = l ^ (k + 3) * (∑ i, ∫ ω, max (X i ω) 0 ^ (k + 3) ∂P) / ((k + 3)! : ℝ) := by
          simp only [a]; rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ l ^ (k + 3) * (((k + 3)! : ℝ) * v * c ^ (k + 1) / 2) / ((k + 3)! : ℝ) := by
          gcongr
      _ = b k := by
          simp only [b]; field_simp; ring
  have hab : ∀ i k, a i k ≤ b k := fun i k =>
    le_trans (Finset.single_le_sum (fun j _ => ha0 j k) (Finset.mem_univ i)) (hsum_ab k)
  have hb_sum : Summable b := (summable_geometric_of_lt_one hr0 hcl).mul_left _
  have ha_sum : ∀ i, Summable (a i) := fun i => Summable.of_nonneg_of_le (ha0 i) (hab i) hb_sum
  have hsingle := fun i => single (X i) (hL2 i) hl.le
    (fun k => hint i (k + 3) (by omega)) (ha_sum i)
  -- the centered summands
  set Z : ι → Ω → ℝ := fun i ω => X i ω - m i with hZ
  have hZind : iIndepFun Z P :=
    hindep.comp (fun i x => x - m i) (fun i => measurable_id.sub_const _)
  have hZm : ∀ i, AEMeasurable (Z i) P := fun i =>
    (hL2 i).aestronglyMeasurable.aemeasurable.sub_const _
  have hZexp : ∀ i, Integrable (fun ω => exp (l * Z i ω)) P := fun i => by
    have : (fun ω => exp (l * Z i ω)) = fun ω => exp (l * X i ω) * exp (-(l * m i)) := by
      funext ω; rw [← Real.exp_add]; congr 1; simp only [Z]; ring
    rw [this]; exact (hsingle i).1.mul_const _
  have hS : (fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) = ∑ i, Z i := by
    funext ω; simp [Z, m, Finset.sum_apply]
  refine ⟨?_, ?_⟩
  · have h := integrable_exp_mul_sum₀ hZind hZm hZexp Finset.univ
    rw [← hS] at h
    exact h
  rw [hS]
  rw [hZind.cgf_sum₀ hZm (fun i _ => hZexp i)]
  -- per-summand cgf bound
  have hcgf : ∀ i, cgf (Z i) P l ≤ l ^ 2 / 2 * ∫ ω, X i ω ^ 2 ∂P + ∑' k, a i k := fun i => by
    set M := ∫ ω, exp (l * X i ω) ∂P
    have hMpos : 0 < M := integral_exp_pos (hsingle i).1
    have hmgf : mgf (Z i) P l = exp (-(l * m i)) * M := by
      simp only [mgf, Z]
      rw [← integral_const_mul]
      congr 1; funext ω; rw [← Real.exp_add]; congr 1; ring
    have hlog : cgf (Z i) P l = -(l * m i) + Real.log M := by
      simp only [cgf]; rw [hmgf, Real.log_mul (exp_pos _).ne' hMpos.ne', Real.log_exp]
    rw [hlog]
    have h1 := Real.log_le_sub_one_of_pos hMpos
    have h2 := (hsingle i).2
    simp only [m] at h2 ⊢
    simp only [a]
    linarith
  calc ∑ i, cgf (Z i) P l ≤ ∑ i, (l ^ 2 / 2 * ∫ ω, X i ω ^ 2 ∂P + ∑' k, a i k) :=
        Finset.sum_le_sum fun i _ => hcgf i
    _ = l ^ 2 / 2 * ∑ i, ∫ ω, X i ω ^ 2 ∂P + ∑' k, ∑ i, a i k := by
        rw [Finset.sum_add_distrib, Finset.mul_sum,
          Summable.tsum_finsetSum (fun i _ => ha_sum i)]
    _ ≤ l ^ 2 / 2 * v + ∑' k, b k :=
        add_le_add (mul_le_mul_of_nonneg_left hv (by positivity))
          (Summable.tsum_le_tsum hsum_ab (summable_sum fun i _ => ha_sum i) hb_sum)
    _ = v * l ^ 2 / (2 * (1 - c * l)) := by
        have h1r : 1 - c * l ≠ 0 := by linarith
        simp only [b]
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hcl]
        rw [eq_div_iff (mul_ne_zero two_ne_zero h1r)]
        have : (1 - c * l)⁻¹ * (1 - c * l) = 1 := inv_mul_cancel₀ h1r
        linear_combination (v * l ^ 2 / 2 * (c * l)) * 2 * this

end MGF
end BernsteinLean
