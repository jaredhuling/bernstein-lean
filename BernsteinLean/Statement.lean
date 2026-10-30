/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import BernsteinLean.General
public import BernsteinLean.Bounded
public import BernsteinLean.Product

/-!
# Bernstein's inequality: public statements

Reference: S. Boucheron, G. Lugosi and P. Massart (2013), *Concentration Inequalities: A
Nonasymptotic Theory of Independence*, Oxford University Press, Section 2.8: Theorem 2.10,
Corollary 2.11, and display (2.10) with the remark after Corollary 2.11.

Let `ι` be a finite index type, let `P` be a probability measure on `Ω`, and suppose that
`X : ι → Ω → ℝ` is an independent family (`iIndepFun X P`) whose laws may differ. The centered
sum is `S ω = Σᵢ (Xᵢ ω - E Xᵢ)`, written out in every statement as
`∑ i, (X i ω - ∫ ω', X i ω' ∂P)`. The parameter called `λ` in the book is `l` here.

Moment conditions of Theorem 2.10 (premises `hL2`, `hv`, `hc`, `hint`, `hmom`):

* `hL2 : ∀ i, MemLp (X i) 2 P` (finite second moments; this also gives measurability);
* `hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v` (`v` is an upper bound on the sum of raw second moments);
* `hc : 0 ≤ c` (the book assumes `c > 0`);
* `hint : ∀ i q, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P`;
* `hmom : ∀ q, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2`.

The assumptions `hL2` and `hint` establish that the expectations in the moment conditions
are finite. These assumptions are explicit because Lean defines the Bochner integral as
zero for a nonintegrable function.

### Degenerate cases

* `v = 0`: the premises force every `Xᵢ` to vanish almost surely, so `S = 0` almost surely.
  The tail bounds are then proved directly; `bernstein_tail_sqrt` needs `0 < v ∨ 0 < c`
  (`hvc`), because with `v = c = 0` the event `{S ≥ 0}` has probability `1`. The strict-event
  variant `bernstein_tail_sqrt_strict` needs no such premise.
* `c = 0` is allowed (the book requires `c > 0`); then `cλ < 1` holds for every `λ`.
* `t > 0` is a premise of every tail bound (as in the book).
* Empty `ι`: `S = 0`; no premise beyond those listed here is needed.
* Bounded forms assume `0 ≤ b`; the non-strict square-root forms also assume `0 < v ∨ 0 < b`.
* `bernstein_iid_mean` assumes `0 < n`; for `n = 0` Lean's `x / 0 = 0` makes the event
  `{|∫ f| > 0}`, which can have probability `1`.

### Proof structure

The module `BernsteinLean.MGF` proves the CGF bound using the exponential-series bound for
each summand, interchange of expectation and summation, `log u ≤ u - 1`, and independence.
The module `BernsteinLean.General` then applies Chernoff's inequality at the specified
admissible `λ`. The bounded moment conditions follow in `BernsteinLean.Bounded`, and the
coordinate projection identities in `BernsteinLean.Product` yield the product-measure forms.
-/

public section

open MeasureTheory ProbabilityTheory Real Nat
open scoped ENNReal

namespace BernsteinLean

/-! ## Theorem 2.10 and Corollary 2.11 under the moment conditions -/

section MomentConditions

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [Fintype ι]

/-- **Bernstein's inequality, CGF bound** (Theorem 2.10). Under the moment conditions, for
`0 < λ` with `cλ < 1`, `ψ_S(λ) = log E e^{λS} ≤ vλ²/(2(1 - cλ))`.
Integrability of `e^{λS}` is `bernstein_integrable_exp`. -/
theorem bernstein_cgf (X : ι → Ω → ℝ) (hindep : iIndepFun X P) (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (l : ℝ) (hl : 0 < l) (hcl : c * l < 1) :
    cgf (fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) P l ≤ v * l ^ 2 / (2 * (1 - c * l)) :=
  (MGF.cgf_le X hindep hL2 hc hl hcl hv hint hmom).2

/-- Under the hypotheses of `bernstein_cgf`, `e^{λS}` is integrable, so the moment generating
function in `bernstein_cgf` is finite and positive. -/
theorem bernstein_integrable_exp (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (l : ℝ) (hl : 0 < l) (hcl : c * l < 1) :
    Integrable (fun ω => exp (l * ∑ i, (X i ω - ∫ ω', X i ω' ∂P))) P :=
  (MGF.cgf_le X hindep hL2 hc hl hcl hv hint hmom).1

/-- **Bernstein's inequality, tail form** (Theorem 2.10). Under the moment conditions, for
`t > 0`, `P{S ≥ √(2vt) + ct} ≤ e^{-t}`. Requires `0 < v ∨ 0 < c` (the book assumes both); with
`v = c = 0` the bound is false. -/
theorem bernstein_tail_sqrt (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (hvc : 0 < v ∨ 0 < c) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + c * t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t)) :=
  General.tail_sqrt X hindep hL2 hc hv hint hmom t ht hvc

/-- Strict-event variant of `bernstein_tail_sqrt`: `P{S > √(2vt) + ct} ≤ e^{-t}` for `t > 0`,
with no positivity premise on `v` or `c`. -/
theorem bernstein_tail_sqrt_strict (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + c * t < ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t)) :=
  General.tail_sqrt_strict X hindep hL2 hc hv hint hmom t ht

/-- **Bernstein's inequality** (Corollary 2.11). Under the moment conditions, for `t > 0`,
`P{S ≥ t} ≤ exp(-t²/(2(v + ct)))`. If `v = c = 0` the right side is `exp 0 = 1` by Lean's
`x / 0 = 0`. -/
theorem bernstein_tail (X : ι → Ω → ℝ) (hindep : iIndepFun X P) (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + c * t))))) :=
  General.tail X hindep hL2 hc hv hint hmom t ht

end MomentConditions

/-! ## Bounded summands: display (2.10) -/

section Bounded

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [Fintype ι]

/-- **Bernstein's inequality for summands bounded above** (display (2.10)). If `Xᵢ ≤ b` almost
surely with `b ≥ 0`, `Xᵢ ∈ L²` and `Σᵢ E Xᵢ² ≤ v`, then for `t > 0`,
`P{S ≥ t} ≤ exp(-t²/(2(v + bt/3)))`. -/
theorem bernstein_bounded_tail (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (b v : ℝ) (hb : 0 ≤ b) (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ b)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
  have h := General.tail X hindep hL2 (c := b / 3) (by positivity) hv
    (Bounded.integrable_max_pow X hL2 hb hXb) (Bounded.moment_condition X hL2 hb hXb hv) t ht
  rwa [show b / 3 * t = b * t / 3 by ring] at h

/-- **Bernstein's inequality for summands bounded above, tail form.** If `Xᵢ ≤ b` almost surely
with `b ≥ 0`, `Xᵢ ∈ L²`, `Σᵢ E Xᵢ² ≤ v`, and `0 < v ∨ 0 < b`, then for `t > 0`,
`P{S ≥ √(2vt) + bt/3} ≤ e^{-t}`. -/
theorem bernstein_bounded_tail_sqrt (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (b v : ℝ) (hb : 0 ≤ b) (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ b)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (hvb : 0 < v ∨ 0 < b) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + b * t / 3 ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t)) := by
  have h := General.tail_sqrt X hindep hL2 (c := b / 3) (by positivity) hv
    (Bounded.integrable_max_pow X hL2 hb hXb) (Bounded.moment_condition X hL2 hb hXb hv) t ht
    (hvb.imp id fun h => by positivity)
  rwa [show b / 3 * t = b * t / 3 by ring] at h

/-- Strict-event variant of `bernstein_bounded_tail_sqrt`, with no premise `0 < v ∨ 0 < b`. -/
theorem bernstein_bounded_tail_sqrt_strict (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (b v : ℝ) (hb : 0 ≤ b) (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ b)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + b * t / 3 < ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t)) := by
  have h := General.tail_sqrt_strict X hindep hL2 (c := b / 3) (by positivity) hv
    (Bounded.integrable_max_pow X hL2 hb hXb) (Bounded.moment_condition X hL2 hb hXb hv) t ht
  rwa [show b / 3 * t = b * t / 3 by ring] at h

/-! ### Two-sided forms -/

omit [IsProbabilityMeasure P] [Fintype ι] in
/-- An almost-sure absolute envelope gives a finite second moment. -/
private lemma memLp_of_abs_le {X : ι → Ω → ℝ} [IsFiniteMeasure P]
    (hXm : ∀ i, AEMeasurable (X i) P) {b : ℝ} (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (i : ι) :
    MemLp (X i) 2 P :=
  MemLp.of_bound (hXm i).aestronglyMeasurable b (by simpa [Real.norm_eq_abs] using hXb i)

omit [IsProbabilityMeasure P] in
/-- Negating every summand negates the centered sum. -/
private lemma neg_sum (X : ι → Ω → ℝ) (ω : Ω) :
    ∑ i, ((fun i ω => -X i ω) i ω - ∫ ω', (fun i ω => -X i ω) i ω' ∂P)
      = -∑ i, (X i ω - ∫ ω', X i ω' ∂P) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_neg]; ring

omit [IsProbabilityMeasure P] in
/-- Negation preserves the sum of raw second moments. -/
private lemma neg_sq_sum (X : ι → Ω → ℝ) :
    ∑ i, ∫ ω, (fun i ω => -X i ω) i ω ^ 2 ∂P = ∑ i, ∫ ω, X i ω ^ 2 ∂P := by
  simp only [neg_sq]

omit [IsProbabilityMeasure P] in
/-- Union bound for a two-sided event. -/
private lemma two_sided_of {S : Ω → ℝ} {a e : ℝ} (strict : Bool)
    (hpos : P {ω | if strict then a < S ω else a ≤ S ω} ≤ ENNReal.ofReal e)
    (hneg : P {ω | if strict then a < -S ω else a ≤ -S ω} ≤ ENNReal.ofReal e) (he : 0 ≤ e) :
    P {ω | if strict then a < |S ω| else a ≤ |S ω|} ≤ ENNReal.ofReal (2 * e) := by
  have hsub : {ω | if strict then a < |S ω| else a ≤ |S ω|} ⊆
      {ω | if strict then a < S ω else a ≤ S ω} ∪
        {ω | if strict then a < -S ω else a ≤ -S ω} := by
    intro ω hω
    cases strict
    · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
      exact (le_abs'.1 hω).elim (fun h => Or.inr (by linarith)) Or.inl
    · simp only [↓reduceIte, Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
      exact lt_abs.1 hω
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal e + ENNReal.ofReal e := add_le_add hpos hneg
    _ = ENNReal.ofReal (2 * e) := by
        rw [← ENNReal.ofReal_add he he]; congr 1; ring

/-- **Two-sided Bernstein inequality for bounded summands.** If `|Xᵢ| ≤ b` almost surely,
`Xᵢ` is almost everywhere measurable, `b ≥ 0`, and `Σᵢ E Xᵢ² ≤ v`, then for `t > 0`,
`P{|S| ≥ t} ≤ 2 exp(-t²/(2(v + bt/3)))`. (`b ≥ 0` follows from the bound when `ι` is
nonempty; it is a premise so that the empty index type needs no separate treatment.) -/
theorem bernstein_bounded_two_sided (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hXm : ∀ i, AEMeasurable (X i) P) (b v : ℝ) (hb : 0 ≤ b)
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ |∑ i, (X i ω - ∫ ω', X i ω' ∂P)|}
      ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
  have hL2 := memLp_of_abs_le hXm hXb
  have hpos := bernstein_bounded_tail X hindep hL2 b v hb
    (fun i => (hXb i).mono fun ω h => (abs_le.1 h).2) hv t ht
  have hneg := bernstein_bounded_tail (fun i ω => -X i ω)
    (hindep.comp (fun _ x => -x) fun _ => measurable_neg) (fun i => (hL2 i).neg) b v hb
    (fun i => (hXb i).mono fun ω h => by have := (abs_le.1 h).1; linarith)
    (by rw [neg_sq_sum]; exact hv) t ht
  simp only [neg_sum] at hneg
  exact two_sided_of (S := fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) false hpos hneg
    (exp_pos _).le

/-- **Two-sided Bernstein inequality for bounded summands, tail form.** Under the hypotheses of
`bernstein_bounded_two_sided` and `0 < v ∨ 0 < b`, for `t > 0`,
`P{|S| ≥ √(2vt) + bt/3} ≤ 2e^{-t}`. -/
theorem bernstein_bounded_two_sided_sqrt (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hXm : ∀ i, AEMeasurable (X i) P) (b v : ℝ) (hb : 0 ≤ b)
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hvb : 0 < v ∨ 0 < b) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + b * t / 3 ≤ |∑ i, (X i ω - ∫ ω', X i ω' ∂P)|}
      ≤ ENNReal.ofReal (2 * exp (-t)) := by
  have hL2 := memLp_of_abs_le hXm hXb
  have hpos := bernstein_bounded_tail_sqrt X hindep hL2 b v hb
    (fun i => (hXb i).mono fun ω h => (abs_le.1 h).2) hv hvb t ht
  have hneg := bernstein_bounded_tail_sqrt (fun i ω => -X i ω)
    (hindep.comp (fun _ x => -x) fun _ => measurable_neg) (fun i => (hL2 i).neg) b v hb
    (fun i => (hXb i).mono fun ω h => by have := (abs_le.1 h).1; linarith)
    (by rw [neg_sq_sum]; exact hv) hvb t ht
  simp only [neg_sum] at hneg
  exact two_sided_of (S := fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) false hpos hneg
    (exp_pos _).le

/-- Strict-event variant of `bernstein_bounded_two_sided_sqrt`, with no premise
`0 < v ∨ 0 < b`: `P{|S| > √(2vt) + bt/3} ≤ 2e^{-t}`. -/
theorem bernstein_bounded_two_sided_sqrt_strict (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hXm : ∀ i, AEMeasurable (X i) P) (b v : ℝ) (hb : 0 ≤ b)
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + b * t / 3 < |∑ i, (X i ω - ∫ ω', X i ω' ∂P)|}
      ≤ ENNReal.ofReal (2 * exp (-t)) := by
  have hL2 := memLp_of_abs_le hXm hXb
  have hpos := bernstein_bounded_tail_sqrt_strict X hindep hL2 b v hb
    (fun i => (hXb i).mono fun ω h => (abs_le.1 h).2) hv t ht
  have hneg := bernstein_bounded_tail_sqrt_strict (fun i ω => -X i ω)
    (hindep.comp (fun _ x => -x) fun _ => measurable_neg) (fun i => (hL2 i).neg) b v hb
    (fun i => (hXb i).mono fun ω h => by have := (abs_le.1 h).1; linarith)
    (by rw [neg_sq_sum]; exact hv) t ht
  simp only [neg_sum] at hneg
  exact two_sided_of (S := fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) true hpos hneg
    (exp_pos _).le

end Bounded

/-! ## Product-measure forms -/

section Product

variable {ι : Type*} [Fintype ι] {E : Type*} [MeasurableSpace E]

/-- Centering coordinate functions agrees with centering under their marginal laws. -/
private lemma centered_eq (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) (x : ι → E) :
    ∑ i, (f i (x i) - ∫ x', f i (x' i) ∂(Measure.pi μ)) = ∑ i, (f i (x i) - ∫ y, f i y ∂(μ i)) :=
  Finset.sum_congr rfl fun i _ => by rw [Product.integral_eval μ (hf i)]

/-- Coordinate second moments agree with their marginal second moments. -/
private lemma sq_eq (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) :
    ∑ i, ∫ x, f i (x i) ^ 2 ∂(Measure.pi μ) = ∑ i, ∫ y, f i y ^ 2 ∂(μ i) :=
  Finset.sum_congr rfl fun i _ =>
    Product.integral_eval μ (g := fun y => f i y ^ 2) ((hf i).pow 2)

/-- **Bernstein's inequality for summands bounded above, product-measure form.** Coordinates
`x i` are independent with laws `μ i` (possibly different); `f i ∈ L²(μ i)`, `f i ≤ b`
`μ i`-almost everywhere, `b ≥ 0`, and `Σᵢ ∫ (f i)² dμ i ≤ v`. For `t > 0`,
`P{Σᵢ (f i (x i) - ∫ f i dμ i) ≥ t} ≤ exp(-t²/(2(v + bt/3)))`. -/
theorem bernstein_bounded_tail_pi (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hL2 : ∀ i, MemLp (f i) 2 (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), f i y ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ ∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))}
      ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
  have hm := fun i => (hL2 i).aestronglyMeasurable
  have h := bernstein_bounded_tail (fun i (x : ι → E) => f i (x i))
    (Product.indep μ fun i => (hm i).aemeasurable) (fun i => Product.memLp μ (hL2 i)) b v hb
    (fun i => Product.ae_eval μ (hfb i)) (by rw [sq_eq μ f hm]; exact hv) t ht
  simpa only [centered_eq μ f hm] using h

/-- **Bernstein's inequality for summands bounded above, product-measure tail form.** Under the
hypotheses of `bernstein_bounded_tail_pi` and `0 < v ∨ 0 < b`, for `t > 0`,
`P{Σᵢ (f i (x i) - ∫ f i dμ i) ≥ √(2vt) + bt/3} ≤ e^{-t}`. -/
theorem bernstein_bounded_tail_sqrt_pi (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hL2 : ∀ i, MemLp (f i) 2 (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), f i y ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (hvb : 0 < v ∨ 0 < b) (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | √(2 * v * t) + b * t / 3 ≤ ∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))}
      ≤ ENNReal.ofReal (exp (-t)) := by
  have hm := fun i => (hL2 i).aestronglyMeasurable
  have h := bernstein_bounded_tail_sqrt (fun i (x : ι → E) => f i (x i))
    (Product.indep μ fun i => (hm i).aemeasurable) (fun i => Product.memLp μ (hL2 i)) b v hb
    (fun i => Product.ae_eval μ (hfb i)) (by rw [sq_eq μ f hm]; exact hv) hvb t ht
  simpa only [centered_eq μ f hm] using h

/-- **Two-sided Bernstein inequality, product-measure form.** `f i` is `μ i`-almost everywhere
measurable with `|f i| ≤ b` `μ i`-almost everywhere, `b ≥ 0`, and `Σᵢ ∫ (f i)² dμ i ≤ v`. For
`t > 0`, `P{|Σᵢ (f i (x i) - ∫ f i dμ i)| ≥ t} ≤ 2 exp(-t²/(2(v + bt/3)))`. -/
theorem bernstein_bounded_two_sided_pi (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hfm : ∀ i, AEMeasurable (f i) (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), |f i y| ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ |∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))|}
      ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
  have hm := fun i => (hfm i).aestronglyMeasurable
  have h := bernstein_bounded_two_sided (fun i (x : ι → E) => f i (x i))
    (Product.indep μ hfm) (Product.aemeasurable μ hfm) b v hb
    (fun i => Product.ae_eval μ (hfb i)) (by rw [sq_eq μ f hm]; exact hv) t ht
  simpa only [centered_eq μ f hm] using h

/-- **Two-sided Bernstein inequality, product-measure tail form.** Under the hypotheses of
`bernstein_bounded_two_sided_pi` and `0 < v ∨ 0 < b`, for `t > 0`,
`P{|Σᵢ (f i (x i) - ∫ f i dμ i)| ≥ √(2vt) + bt/3} ≤ 2e^{-t}`. -/
theorem bernstein_bounded_two_sided_sqrt_pi (μ : ι → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hfm : ∀ i, AEMeasurable (f i) (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), |f i y| ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (hvb : 0 < v ∨ 0 < b) (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | √(2 * v * t) + b * t / 3 ≤ |∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))|}
      ≤ ENNReal.ofReal (2 * exp (-t)) := by
  have hm := fun i => (hfm i).aestronglyMeasurable
  have h := bernstein_bounded_two_sided_sqrt (fun i (x : ι → E) => f i (x i))
    (Product.indep μ hfm) (Product.aemeasurable μ hfm) b v hb
    (fun i => Product.ae_eval μ (hfb i)) (by rw [sq_eq μ f hm]; exact hv) hvb t ht
  simpa only [centered_eq μ f hm] using h

/-- Strict-event variant of `bernstein_bounded_two_sided_sqrt_pi`, with no premise
`0 < v ∨ 0 < b`. -/
theorem bernstein_bounded_two_sided_sqrt_strict_pi (μ : ι → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hfm : ∀ i, AEMeasurable (f i) (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), |f i y| ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | √(2 * v * t) + b * t / 3 < |∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))|}
      ≤ ENNReal.ofReal (2 * exp (-t)) := by
  have hm := fun i => (hfm i).aestronglyMeasurable
  have h := bernstein_bounded_two_sided_sqrt_strict (fun i (x : ι → E) => f i (x i))
    (Product.indep μ hfm) (Product.aemeasurable μ hfm) b v hb
    (fun i => Product.ae_eval μ (hfb i)) (by rw [sq_eq μ f hm]; exact hv) t ht
  simpa only [centered_eq μ f hm] using h

end Product

/-! ## The i.i.d. empirical-mean form -/

section IID

variable {E : Type*} [MeasurableSpace E]

/-- Rescaling of the threshold: `n (√(2 I t/n) + Bt/(3n)) = √(2 (n I) t) + Bt/3` for `n > 0`. -/
private lemma threshold_scale {n : ℝ} (hn : 0 < n) (I B t : ℝ) :
    n * (√(2 * I * t / n) + B * t / (3 * n)) = √(2 * (n * I) * t) + B * t / 3 := by
  have hsq : n * √(2 * I * t / n) = √(2 * (n * I) * t) := by
    have h1 : √(2 * (n * I) * t) = √(n ^ 2 * (2 * I * t / n)) := by
      congr 1; field_simp
    rw [h1, Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]
  rw [mul_add, hsq]; congr 1; field_simp

/-- Rescaling of the deviation: `n |(1/n) Σ aᵢ - m| = |Σ (aᵢ - m)|` for `n > 0`. -/
private lemma deviation_scale {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (m : ℝ) :
    (n : ℝ) * |(1 / (n : ℝ)) * ∑ i, a i - m| = |∑ i, (a i - m)| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← abs_of_pos hn', ← abs_mul, abs_of_pos hn', Finset.sum_sub_distrib]
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Bernstein's inequality for an i.i.d. empirical mean.** This is the two-sided form of
Theorem 2.10 of Boucheron, Lugosi and Massart (2013), whose conditions hold with
`v = n ∫ f² dμ` and `c = B/3` by the remark after their Corollary 2.11, applied to
`f(xᵢ)` and `-f(xᵢ)` with a union bound and divided by `n`.

Let `x₁, …, xₙ` be i.i.d. with law `μ` (product measure `Measure.pi (fun _ : Fin n => μ)`),
`n > 0`, and let `f` be `μ`-almost everywhere measurable with `0 ≤ f ≤ B` `μ`-almost
everywhere. For `t > 0`,
`P{|(1/n) Σᵢ f(xᵢ) - ∫ f dμ| > √(2 (∫ f² dμ) t/n) + Bt/(3n)} ≤ 2e^{-t}`.
No positivity premise on `B` is needed (`B ≥ 0` follows from the bounds); `n > 0` is needed
(see the module docstring). -/
theorem bernstein_iid_mean (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (hf : AEMeasurable f μ) (B : ℝ) (hf0 : ∀ᵐ y ∂μ, 0 ≤ f y)
    (hfB : ∀ᵐ y ∂μ, f y ≤ B) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => μ)
        {x | √(2 * (∫ y, f y ^ 2 ∂μ) * t / n) + B * t / (3 * n)
          < |(1 / (n : ℝ)) * ∑ i, f (x i) - ∫ y, f y ∂μ|}
      ≤ ENNReal.ofReal (2 * exp (-t)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨y₀, hy₀⟩ := (hf0.and hfB).exists
  have hB : 0 ≤ B := hy₀.1.trans hy₀.2
  have habs : ∀ᵐ y ∂μ, |f y| ≤ B := (hf0.and hfB).mono fun y h => abs_le.2 ⟨by linarith [h.1], h.2⟩
  have h := bernstein_bounded_two_sided_sqrt_strict_pi (fun _ : Fin n => μ) (fun _ => f)
    (fun _ => hf) B (n * ∫ y, f y ^ 2 ∂μ) hB (fun _ => habs)
    (by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]) t ht
  refine le_trans (measure_mono ?_) h
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [← threshold_scale hn', ← deviation_scale hn]
  exact mul_lt_mul_of_pos_left hx hn'

/-- Non-strict-event version of `bernstein_iid_mean`:
`P{|(1/n) Σᵢ f(xᵢ) - ∫ f dμ| ≥ √(2 (∫ f² dμ) t/n) + Bt/(3n)} ≤ 2e^{-t}`. It assumes `0 < B`:
if `B = 0` then `f = 0` almost everywhere, the threshold is `0`, and the event has
probability `1`. -/
theorem bernstein_iid_mean_ge (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (hf : AEMeasurable f μ) (B : ℝ) (hB : 0 < B) (hf0 : ∀ᵐ y ∂μ, 0 ≤ f y)
    (hfB : ∀ᵐ y ∂μ, f y ≤ B) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => μ)
        {x | √(2 * (∫ y, f y ^ 2 ∂μ) * t / n) + B * t / (3 * n)
          ≤ |(1 / (n : ℝ)) * ∑ i, f (x i) - ∫ y, f y ∂μ|}
      ≤ ENNReal.ofReal (2 * exp (-t)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have habs : ∀ᵐ y ∂μ, |f y| ≤ B := (hf0.and hfB).mono fun y h => abs_le.2 ⟨by linarith [h.1], h.2⟩
  have h := bernstein_bounded_two_sided_sqrt_pi (fun _ : Fin n => μ) (fun _ => f)
    (fun _ => hf) B (n * ∫ y, f y ^ 2 ∂μ) hB.le (fun _ => habs)
    (by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]) (Or.inr hB)
    t ht
  refine le_trans (measure_mono ?_) h
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [← threshold_scale hn', ← deviation_scale hn]
  exact mul_le_mul_of_nonneg_left hx hn'.le

end IID

end BernsteinLean
