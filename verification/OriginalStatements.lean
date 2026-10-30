/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import Lean
import BernsteinLean

/-! # Regression checks for the original 18 public theorem types

The expected elaborated types were frozen before the release refactor on 2026-10-30.
The check requires definitional equality, not merely an implication between statements.
-/

open Lean Meta Elab Command MeasureTheory ProbabilityTheory Real
universe u_1 u_2 u_3

elab "assert_original_type " name:ident " : " expected:term : command => do
  liftTermElabM do
    let expectedType ← Term.elabType expected
    let actualType ← inferType (← mkConstWithFreshMVarLevels name.getId)
    unless ← isDefEq actualType expectedType do
      throwError "Public theorem type changed: {name.getId}"

assert_original_type BernsteinLean.bernstein_cgf :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), MemLp (X i) 2 P) →
      ∀ (v c : ℝ),
        0 ≤ c →
          ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
            (∀ (i : ι) (q : ℕ), 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P) →
              (∀ (q : ℕ), 3 ≤ q → ∑ i, ∫ (ω : Ω), max (X i ω) 0 ^ q ∂P ≤ (Nat.factorial q : ℝ) * v * c ^ (q - 2) / 2) →
                ∀ (l : ℝ),
                  0 < l →
                    c * l < 1 → cgf (fun ω => ∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)) P l ≤ v * l ^ 2 / (2 * (1 - c * l)))

assert_original_type BernsteinLean.bernstein_integrable_exp :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), MemLp (X i) 2 P) →
      ∀ (v c : ℝ),
        0 ≤ c →
          ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
            (∀ (i : ι) (q : ℕ), 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P) →
              (∀ (q : ℕ), 3 ≤ q → ∑ i, ∫ (ω : Ω), max (X i ω) 0 ^ q ∂P ≤ (Nat.factorial q : ℝ) * v * c ^ (q - 2) / 2) →
                ∀ (l : ℝ), 0 < l → c * l < 1 → Integrable (fun ω => rexp (l * ∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P))) P)

assert_original_type BernsteinLean.bernstein_tail_sqrt :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), MemLp (X i) 2 P) →
      ∀ (v c : ℝ),
        0 ≤ c →
          ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
            (∀ (i : ι) (q : ℕ), 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P) →
              (∀ (q : ℕ), 3 ≤ q → ∑ i, ∫ (ω : Ω), max (X i ω) 0 ^ q ∂P ≤ (Nat.factorial q : ℝ) * v * c ^ (q - 2) / 2) →
                0 < v ∨ 0 < c →
                  ∀ (t : ℝ),
                    0 < t →
                      P {ω | √(2 * v * t) + c * t ≤ ∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)} ≤ ENNReal.ofReal (rexp (-t)))

assert_original_type BernsteinLean.bernstein_tail_sqrt_strict :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), MemLp (X i) 2 P) →
      ∀ (v c : ℝ),
        0 ≤ c →
          ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
            (∀ (i : ι) (q : ℕ), 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P) →
              (∀ (q : ℕ), 3 ≤ q → ∑ i, ∫ (ω : Ω), max (X i ω) 0 ^ q ∂P ≤ (Nat.factorial q : ℝ) * v * c ^ (q - 2) / 2) →
                ∀ (t : ℝ),
                  0 < t →
                    P {ω | √(2 * v * t) + c * t < ∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)} ≤ ENNReal.ofReal (rexp (-t)))

assert_original_type BernsteinLean.bernstein_tail :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), MemLp (X i) 2 P) →
      ∀ (v c : ℝ),
        0 ≤ c →
          ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
            (∀ (i : ι) (q : ℕ), 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P) →
              (∀ (q : ℕ), 3 ≤ q → ∑ i, ∫ (ω : Ω), max (X i ω) 0 ^ q ∂P ≤ (Nat.factorial q : ℝ) * v * c ^ (q - 2) / 2) →
                ∀ (t : ℝ),
                  0 < t →
                    P {ω | t ≤ ∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)} ≤
                      ENNReal.ofReal (rexp (-(t ^ 2 / (2 * (v + c * t))))))

assert_original_type BernsteinLean.bernstein_bounded_tail :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), MemLp (X i) 2 P) →
      ∀ (b v : ℝ),
        0 ≤ b →
          (∀ (i : ι), ∀ᵐ (ω : Ω) ∂P, X i ω ≤ b) →
            ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
              ∀ (t : ℝ),
                0 < t →
                  P {ω | t ≤ ∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)} ≤
                    ENNReal.ofReal (rexp (-(t ^ 2 / (2 * (v + b * t / 3))))))

assert_original_type BernsteinLean.bernstein_bounded_tail_sqrt :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), MemLp (X i) 2 P) →
      ∀ (b v : ℝ),
        0 ≤ b →
          (∀ (i : ι), ∀ᵐ (ω : Ω) ∂P, X i ω ≤ b) →
            ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
              0 < v ∨ 0 < b →
                ∀ (t : ℝ),
                  0 < t →
                    P {ω | √(2 * v * t) + b * t / 3 ≤ ∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)} ≤ ENNReal.ofReal (rexp (-t)))

assert_original_type BernsteinLean.bernstein_bounded_tail_sqrt_strict :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), MemLp (X i) 2 P) →
      ∀ (b v : ℝ),
        0 ≤ b →
          (∀ (i : ι), ∀ᵐ (ω : Ω) ∂P, X i ω ≤ b) →
            ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
              ∀ (t : ℝ),
                0 < t →
                  P {ω | √(2 * v * t) + b * t / 3 < ∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)} ≤ ENNReal.ofReal (rexp (-t)))

assert_original_type BernsteinLean.bernstein_bounded_two_sided :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), AEMeasurable (X i) P) →
      ∀ (b v : ℝ),
        0 ≤ b →
          (∀ (i : ι), ∀ᵐ (ω : Ω) ∂P, |X i ω| ≤ b) →
            ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
              ∀ (t : ℝ),
                0 < t →
                  P {ω | t ≤ |∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)|} ≤
                    ENNReal.ofReal (2 * rexp (-(t ^ 2 / (2 * (v + b * t / 3))))))

assert_original_type BernsteinLean.bernstein_bounded_two_sided_sqrt :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), AEMeasurable (X i) P) →
      ∀ (b v : ℝ),
        0 ≤ b →
          (∀ (i : ι), ∀ᵐ (ω : Ω) ∂P, |X i ω| ≤ b) →
            ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
              0 < v ∨ 0 < b →
                ∀ (t : ℝ),
                  0 < t →
                    P {ω | √(2 * v * t) + b * t / 3 ≤ |∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)|} ≤
                      ENNReal.ofReal (2 * rexp (-t)))

assert_original_type BernsteinLean.bernstein_bounded_two_sided_sqrt_strict :
  (∀ {Ω : Type u_1} [_inst : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type u_2} [_inst_2 : Fintype ι]
  (X : ι → Ω → ℝ),
  iIndepFun X P →
    (∀ (i : ι), AEMeasurable (X i) P) →
      ∀ (b v : ℝ),
        0 ≤ b →
          (∀ (i : ι), ∀ᵐ (ω : Ω) ∂P, |X i ω| ≤ b) →
            ∑ i, ∫ (ω : Ω), X i ω ^ 2 ∂P ≤ v →
              ∀ (t : ℝ),
                0 < t →
                  P {ω | √(2 * v * t) + b * t / 3 < |∑ i, (X i ω - ∫ (ω' : Ω), X i ω' ∂P)|} ≤
                    ENNReal.ofReal (2 * rexp (-t)))

assert_original_type BernsteinLean.bernstein_bounded_tail_pi :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {E : Type u_2} [_inst_1 : MeasurableSpace E] (μ : ι → Measure E)
  [∀ (i : ι), IsProbabilityMeasure (μ i)] (f : ι → E → ℝ),
  (∀ (i : ι), MemLp (f i) 2 (μ i)) →
    ∀ (b v : ℝ),
      0 ≤ b →
        (∀ (i : ι), ∀ᵐ (y : E) ∂μ i, f i y ≤ b) →
          ∑ i, ∫ (y : E), f i y ^ 2 ∂μ i ≤ v →
            ∀ (t : ℝ),
              0 < t →
                (Measure.pi μ) {x | t ≤ ∑ i, (f i (x i) - ∫ (y : E), f i y ∂μ i)} ≤
                  ENNReal.ofReal (rexp (-(t ^ 2 / (2 * (v + b * t / 3))))))

assert_original_type BernsteinLean.bernstein_bounded_tail_sqrt_pi :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {E : Type u_2} [_inst_1 : MeasurableSpace E] (μ : ι → Measure E)
  [∀ (i : ι), IsProbabilityMeasure (μ i)] (f : ι → E → ℝ),
  (∀ (i : ι), MemLp (f i) 2 (μ i)) →
    ∀ (b v : ℝ),
      0 ≤ b →
        (∀ (i : ι), ∀ᵐ (y : E) ∂μ i, f i y ≤ b) →
          ∑ i, ∫ (y : E), f i y ^ 2 ∂μ i ≤ v →
            0 < v ∨ 0 < b →
              ∀ (t : ℝ),
                0 < t →
                  (Measure.pi μ) {x | √(2 * v * t) + b * t / 3 ≤ ∑ i, (f i (x i) - ∫ (y : E), f i y ∂μ i)} ≤
                    ENNReal.ofReal (rexp (-t)))

assert_original_type BernsteinLean.bernstein_bounded_two_sided_pi :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {E : Type u_2} [_inst_1 : MeasurableSpace E] (μ : ι → Measure E)
  [∀ (i : ι), IsProbabilityMeasure (μ i)] (f : ι → E → ℝ),
  (∀ (i : ι), AEMeasurable (f i) (μ i)) →
    ∀ (b v : ℝ),
      0 ≤ b →
        (∀ (i : ι), ∀ᵐ (y : E) ∂μ i, |f i y| ≤ b) →
          ∑ i, ∫ (y : E), f i y ^ 2 ∂μ i ≤ v →
            ∀ (t : ℝ),
              0 < t →
                (Measure.pi μ) {x | t ≤ |∑ i, (f i (x i) - ∫ (y : E), f i y ∂μ i)|} ≤
                  ENNReal.ofReal (2 * rexp (-(t ^ 2 / (2 * (v + b * t / 3))))))

assert_original_type BernsteinLean.bernstein_bounded_two_sided_sqrt_pi :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {E : Type u_2} [_inst_1 : MeasurableSpace E] (μ : ι → Measure E)
  [∀ (i : ι), IsProbabilityMeasure (μ i)] (f : ι → E → ℝ),
  (∀ (i : ι), AEMeasurable (f i) (μ i)) →
    ∀ (b v : ℝ),
      0 ≤ b →
        (∀ (i : ι), ∀ᵐ (y : E) ∂μ i, |f i y| ≤ b) →
          ∑ i, ∫ (y : E), f i y ^ 2 ∂μ i ≤ v →
            0 < v ∨ 0 < b →
              ∀ (t : ℝ),
                0 < t →
                  (Measure.pi μ) {x | √(2 * v * t) + b * t / 3 ≤ |∑ i, (f i (x i) - ∫ (y : E), f i y ∂μ i)|} ≤
                    ENNReal.ofReal (2 * rexp (-t)))

assert_original_type BernsteinLean.bernstein_bounded_two_sided_sqrt_strict_pi :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {E : Type u_2} [_inst_1 : MeasurableSpace E] (μ : ι → Measure E)
  [∀ (i : ι), IsProbabilityMeasure (μ i)] (f : ι → E → ℝ),
  (∀ (i : ι), AEMeasurable (f i) (μ i)) →
    ∀ (b v : ℝ),
      0 ≤ b →
        (∀ (i : ι), ∀ᵐ (y : E) ∂μ i, |f i y| ≤ b) →
          ∑ i, ∫ (y : E), f i y ^ 2 ∂μ i ≤ v →
            ∀ (t : ℝ),
              0 < t →
                (Measure.pi μ) {x | √(2 * v * t) + b * t / 3 < |∑ i, (f i (x i) - ∫ (y : E), f i y ∂μ i)|} ≤
                  ENNReal.ofReal (2 * rexp (-t)))

assert_original_type BernsteinLean.bernstein_iid_mean :
  (∀ {E : Type u_1} [_inst : MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ),
  0 < n →
    ∀ (f : E → ℝ),
      AEMeasurable f μ →
        ∀ (B : ℝ),
          (∀ᵐ (y : E) ∂μ, 0 ≤ f y) →
            (∀ᵐ (y : E) ∂μ, f y ≤ B) →
              ∀ (t : ℝ),
                0 < t →
                  (Measure.pi fun _x => μ)
                      {x |
                        √((2 * ∫ (y : E), f y ^ 2 ∂μ) * t / ↑n) + B * t / (3 * ↑n) <
                          |1 / ↑n * ∑ i, f (x i) - ∫ (y : E), f y ∂μ|} ≤
                    ENNReal.ofReal (2 * rexp (-t)))

assert_original_type BernsteinLean.bernstein_iid_mean_ge :
  (∀ {E : Type u_1} [_inst : MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ),
  0 < n →
    ∀ (f : E → ℝ),
      AEMeasurable f μ →
        ∀ (B : ℝ),
          0 < B →
            (∀ᵐ (y : E) ∂μ, 0 ≤ f y) →
              (∀ᵐ (y : E) ∂μ, f y ≤ B) →
                ∀ (t : ℝ),
                  0 < t →
                    (Measure.pi fun _x => μ)
                        {x |
                          √((2 * ∫ (y : E), f y ^ 2 ∂μ) * t / ↑n) + B * t / (3 * ↑n) ≤
                            |1 / ↑n * ∑ i, f (x i) - ∫ (y : E), f y ∂μ|} ≤
                      ENNReal.ofReal (2 * rexp (-t)))

