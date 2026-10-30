# bernstein-lean

Bernstein's inequality bounds deviations of a sum of independent random variables from its expectation through conditions on their moments. This library formalizes the cumulant generating function (CGF) bound and the associated tail inequalities in Lean 4 with mathlib. It includes bounded-summand, two-sided, product-measure, and empirical-mean forms, together with corollaries expressed in terms of variances and empirical frequencies. The probability laws may differ across summands, and the proof uses mathlib as its only external mathematical dependency.

The formalization follows S. Boucheron, G. Lugosi and P. Massart (2013), [*Concentration Inequalities: A Nonasymptotic Theory of Independence*](https://doi.org/10.1093/acprof:oso/9780199535255.001.0001), Oxford University Press, Section 2.8. Its correspondence with the reference is as follows.

| Result in Section 2.8 | Lean declarations |
| --- | --- |
| Theorem 2.10: CGF bound under moment conditions | `bernstein_cgf` and `bernstein_integrable_exp` |
| Theorem 2.10: square-root deviation bound | `bernstein_tail_sqrt` |
| Corollary 2.11: rational-exponent tail bound | `bernstein_tail` |
| Display (2.10) and the bounded-case remark | `bernstein_bounded_tail` |

The Cramér-transform clause of Theorem 2.10 is outside the formalization. The additional two-sided, product-measure, empirical-mean, variance, and frequency results are derived corollaries. The [comparison with the reference](#relation-to-boucheron-lugosi-and-massart-2013) describes the explicit integrability assumptions and extensions to zero parameters.

## Related formalizations

Zhang, Lee and Liu's [*AI4SLT: Empirical Processes in Lean 4 for Formal Statistical Learning Theory*](https://arxiv.org/abs/2602.02285) (ICML 2026) accompanies the [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) library. Its [scalar Bernstein results](https://github.com/YuanheZ/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/SubGaussian.lean#L163) derive one-sided and two-sided concentration inequalities from a local quadratic CGF bound and exponential integrability. It also contains a [matrix Bernstein inequality](https://github.com/YuanheZ/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/RMT/MatBern.lean#L2889) for independent, centered, almost-sure bounded Hermitian summands. Its one-dimensional specialization overlaps the bounded scalar case.

The present library develops the scalar inequalities from the positive-part moment conditions in Boucheron, Lugosi and Massart, deriving exponential integrability and the CGF bound before proving the tail inequalities. These conditions allow summands that are not bounded. The bounded one-sided results require an upper bound and finite second moments, allowing an unbounded negative part. The scope is therefore a focused implementation of these moment-condition results and their corollaries, with substantial overlap in the bounded case. The comparison above concerns upstream revision `d0f506f0a695018265dccb33bcb05e2f5ca1c876`, which uses Lean 4.32.0; this library uses Lean 4.35.0.

## Mathematical results

Let `P` be a probability measure on a measurable space `Ω`, and let `ι` be a finite index type. The random-variable statements use the following Lean context:

```lean
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [Fintype ι]
```

Suppose that `X : ι → Ω → ℝ` is an independent family, expressed by `iIndepFun X P`. Write `S = Σᵢ (Xᵢ - E Xᵢ)` for the centered sum. The theorem statements express this sum as `∑ i, (X i ω - ∫ ω', X i ω' ∂P)`. The exponential parameter denoted by `λ` in the reference is written as `l` in Lean.

The import `BernsteinLean` provides the results in the namespace of the same name. The moment-condition, bounded, product-measure, and empirical-mean statements are in `BernsteinLean/Statement.lean`. The variance and frequency corollaries are in `Variance.lean` and `Frequency.lean`, and `CGF.lean` defines the exponential-moment condition used in the tail proofs.

### Moment conditions: Theorem 2.10 and Corollary 2.11

The moment-condition results assume that each `Xᵢ` has a finite second moment, that `Σᵢ E Xᵢ² ≤ v`, and that `c ≥ 0`. For each integer `q ≥ 3`, the positive-part power `(Xᵢ)₊^q` must be integrable, and its moments must satisfy `Σᵢ E (Xᵢ)₊^q ≤ q! v c^(q-2)/2`, where `(Xᵢ)₊ = max(Xᵢ, 0)`. These conditions are expressed by `hL2`, `hv`, `hc`, `hint`, and `hmom`, respectively.

```lean
theorem bernstein_cgf (X : ι → Ω → ℝ) (hindep : iIndepFun X P) (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (l : ℝ) (hl : 0 < l) (hcl : c * l < 1) :
    cgf (fun ω => ∑ i, (X i ω - ∫ ω', X i ω' ∂P)) P l ≤ v * l ^ 2 / (2 * (1 - c * l))

theorem bernstein_integrable_exp (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (l : ℝ) (hl : 0 < l) (hcl : c * l < 1) :
    Integrable (fun ω => exp (l * ∑ i, (X i ω - ∫ ω', X i ω' ∂P))) P

theorem bernstein_tail_sqrt (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (hvc : 0 < v ∨ 0 < c) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + c * t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t))

theorem bernstein_tail_sqrt_strict (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + c * t < ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t))

theorem bernstein_tail (X : ι → Ω → ℝ) (hindep : iIndepFun X P) (hL2 : ∀ i, MemLp (X i) 2 P)
    (v c : ℝ) (hc : 0 ≤ c) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hint : ∀ i, ∀ q : ℕ, 3 ≤ q → Integrable (fun ω => max (X i ω) 0 ^ q) P)
    (hmom : ∀ q : ℕ, 3 ≤ q → ∑ i, ∫ ω, max (X i ω) 0 ^ q ∂P ≤ q ! * v * c ^ (q - 2) / 2)
    (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + c * t)))))
```

The CGF result bounds the logarithm of the moment generating function of the centered sum, and `bernstein_integrable_exp` establishes the required exponential integrability. The square-root form specifies a deviation threshold with tail probability at most `exp(-t)`, whereas `bernstein_tail` bounds the probability of a fixed deviation `t`. The distinction between strict and non-strict events is relevant when the parameters are zero, as described under [Degenerate cases](#degenerate-cases).

### Summands bounded above: display (2.10)

If each `Xᵢ` has a finite second moment and satisfies `Xᵢ ≤ b` almost surely for `b ≥ 0`, then the moment conditions hold with `c = b/3`. The parameter `v` can be any upper bound on the sum of raw second moments. This yields the following bounded-summand results.

```lean
theorem bernstein_bounded_tail (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (b v : ℝ) (hb : 0 ≤ b) (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ b)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + b * t / 3)))))

theorem bernstein_bounded_tail_sqrt (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (b v : ℝ) (hb : 0 ≤ b) (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ b)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (hvb : 0 < v ∨ 0 < b) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + b * t / 3 ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t))

theorem bernstein_bounded_tail_sqrt_strict (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (b v : ℝ) (hb : 0 ≤ b) (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ b)
    (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + b * t / 3 < ∑ i, (X i ω - ∫ ω', X i ω' ∂P)}
      ≤ ENNReal.ofReal (exp (-t))
```

### Two-sided bounds

An almost-sure absolute bound `|Xᵢ| ≤ b`, together with almost-everywhere measurability, implies a finite second moment. Applying the one-sided inequalities to `Xᵢ` and `-Xᵢ` and taking a union bound yields the two-sided results.

```lean
theorem bernstein_bounded_two_sided (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hXm : ∀ i, AEMeasurable (X i) P) (b v : ℝ) (hb : 0 ≤ b)
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v) (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ |∑ i, (X i ω - ∫ ω', X i ω' ∂P)|}
      ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 / (2 * (v + b * t / 3)))))

theorem bernstein_bounded_two_sided_sqrt (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hXm : ∀ i, AEMeasurable (X i) P) (b v : ℝ) (hb : 0 ≤ b)
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (hvb : 0 < v ∨ 0 < b) (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + b * t / 3 ≤ |∑ i, (X i ω - ∫ ω', X i ω' ∂P)|}
      ≤ ENNReal.ofReal (2 * exp (-t))

theorem bernstein_bounded_two_sided_sqrt_strict (X : ι → Ω → ℝ) (hindep : iIndepFun X P)
    (hXm : ∀ i, AEMeasurable (X i) P) (b v : ℝ) (hb : 0 ≤ b)
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hv : ∑ i, ∫ ω, X i ω ^ 2 ∂P ≤ v)
    (t : ℝ) (ht : 0 < t) :
    P {ω | √(2 * v * t) + b * t / 3 < |∑ i, (X i ω - ∫ ω', X i ω' ∂P)|}
      ≤ ENNReal.ofReal (2 * exp (-t))
```

### Product-measure forms

Let `E` be a measurable space and let `μ i` be a probability measure on `E` for each `i`. For almost-everywhere measurable `f i`, the coordinate functions `f i (x i)` under `Measure.pi μ` are independent and have expectations `∫ f i dμ i`. The coordinate projections preserve the relevant integrals and almost-sure bounds, which allows the random-variable results to be applied directly on the product space.

```lean
theorem bernstein_bounded_tail_pi (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hL2 : ∀ i, MemLp (f i) 2 (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), f i y ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ ∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))}
      ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * (v + b * t / 3)))))

theorem bernstein_bounded_tail_sqrt_pi (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hL2 : ∀ i, MemLp (f i) 2 (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), f i y ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (hvb : 0 < v ∨ 0 < b) (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | √(2 * v * t) + b * t / 3 ≤ ∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))}
      ≤ ENNReal.ofReal (exp (-t))

theorem bernstein_bounded_two_sided_pi (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hfm : ∀ i, AEMeasurable (f i) (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), |f i y| ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ |∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))|}
      ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 / (2 * (v + b * t / 3)))))

theorem bernstein_bounded_two_sided_sqrt_pi (μ : ι → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hfm : ∀ i, AEMeasurable (f i) (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), |f i y| ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (hvb : 0 < v ∨ 0 < b) (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | √(2 * v * t) + b * t / 3 ≤ |∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))|}
      ≤ ENNReal.ofReal (2 * exp (-t))

theorem bernstein_bounded_two_sided_sqrt_strict_pi (μ : ι → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → E → ℝ) (hfm : ∀ i, AEMeasurable (f i) (μ i)) (b v : ℝ) (hb : 0 ≤ b)
    (hfb : ∀ i, ∀ᵐ y ∂(μ i), |f i y| ≤ b) (hv : ∑ i, ∫ y, f i y ^ 2 ∂(μ i) ≤ v)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | √(2 * v * t) + b * t / 3 < |∑ i, (f i (x i) - ∫ y, f i y ∂(μ i))|}
      ≤ ENNReal.ofReal (2 * exp (-t))
```

### Empirical means

For `n > 0` independent and identically distributed (i.i.d.) draws from `μ` and an almost-everywhere measurable function satisfying `0 ≤ f ≤ B` almost everywhere, the empirical mean satisfies `|ℙₙ f - E f| ≤ √(2 E(f²) t/n) + Bt/(3n)` with probability at least `1 - 2e^(-t)`, for `t > 0`. This follows by applying the two-sided bounded form to `Xᵢ = f(xᵢ)` with `b = B` and `v = n ∫ f² dμ`, then dividing the sum and threshold by `n`.

```lean
theorem bernstein_iid_mean (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (hf : AEMeasurable f μ) (B : ℝ) (hf0 : ∀ᵐ y ∂μ, 0 ≤ f y)
    (hfB : ∀ᵐ y ∂μ, f y ≤ B) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => μ)
        {x | √(2 * (∫ y, f y ^ 2 ∂μ) * t / n) + B * t / (3 * n)
          < |(1 / (n : ℝ)) * ∑ i, f (x i) - ∫ y, f y ∂μ|}
      ≤ ENNReal.ofReal (2 * exp (-t))

theorem bernstein_iid_mean_ge (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (hf : AEMeasurable f μ) (B : ℝ) (hB : 0 < B) (hf0 : ∀ᵐ y ∂μ, 0 ≤ f y)
    (hfB : ∀ᵐ y ∂μ, f y ≤ B) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => μ)
        {x | √(2 * (∫ y, f y ^ 2 ∂μ) * t / n) + B * t / (3 * n)
          ≤ |(1 / (n : ℝ)) * ∑ i, f (x i) - ∫ y, f y ∂μ|}
      ≤ ENNReal.ofReal (2 * exp (-t))
```

### Variance and frequency corollaries

The variance form applies the bounded-summand result to the centered variables. The theorem `bernstein_variance_tail` assumes independent `X i` with finite second moments, `b ≥ 0`, the almost-sure bound `X i − E(X i) ≤ b`, and `Σᵢ Var(X i) ≤ v`. For `t > 0`, it proves

```text
P{Σᵢ (Xᵢ − E Xᵢ) ≥ t} ≤ exp(−t² / (2(v + bt/3))).
```

Thus, the bound on each summand in this result applies after centering. The theorem `bernstein_variance_two_sided_sqrt_strict` uses the absolute bound `|X i − E(X i)| ≤ b` and proves `P{|Σᵢ (Xᵢ − E Xᵢ)| > √(2vt) + bt/3} ≤ 2 exp(−t)`. Its strict event also permits `v = 0` and `b = 0`.

The theorem `bernstein_frequency` applies the empirical-mean result to the indicator of a measurable set `A`. For `n > 0` independent draws from a probability measure `μ`, write `p = μ.real A`. For `t > 0`,

```text
P{|n⁻¹ Σᵢ 1_A(Xᵢ) − p| > √(2pt/n) + t/(3n)} ≤ 2 exp(−t).
```

The threshold uses the indicator's raw second moment `E(1_A²) = p`. A threshold based on the variance `p(1−p)` would require a separate variance calculation. The stated result includes `p = 0` and `p = 1`.

### Cumulant generating function condition

The predicate `HasBernsteinCGF S P v c` requires `v ≥ 0`, `c ≥ 0`, and, for each `λ > 0` with `cλ < 1`, both `Integrable (fun ω => exp (λ * S ω)) P` and `cgf S P λ ≤ vλ² / (2(1−cλ))`. It is stated for `S` without a centering hypothesis. The theorem `General.hasBernsteinCGF` establishes this condition for the centered sum under the moment assumptions above.

The method `.tail_le_exp` applies Chernoff's inequality at an admissible exponential parameter. The methods `.tail_sqrt` and `.tail` establish the two tail forms when `v > 0`. The moment-condition theorems also treat `v = 0`, using the resulting almost-sure equality of each summand to zero. For positive `c`, the restricted range `cλ < 1` gives the one-sided sub-gamma CGF bound used in Bernstein's inequality.

## Relation to Boucheron, Lugosi and Massart (2013)

Theorem 2.10 assumes `v > 0` and `c > 0`. The Lean statements allow `c = 0` and any real `v` satisfying `Σᵢ E Xᵢ² ≤ v`, which implies `v ≥ 0`. The exponential parameter range `λ ∈ (0, 1/c)` is expressed as `0 < λ` and `cλ < 1`. These conditions agree when `c > 0` and permit each `λ > 0` when `c = 0`.

The finite-moment assumptions are explicit because the Bochner integral in Lean is defined as zero for a nonintegrable function. The hypotheses `hL2` and `hint` ensure that the moment inequalities concern finite expectations; `hL2` also implies almost-everywhere measurability. Likewise, mathlib defines `cgf` as the logarithm of `mgf`, and `bernstein_integrable_exp` establishes that the exponential moment is finite and positive. This justifies its interpretation as a cumulant generating function.

The non-strict square-root tail has the event `{S ≥ √(2vt) + ct}` from Theorem 2.10 for `t > 0`. The condition `0 < v ∨ 0 < c` permits either parameter to be zero while excluding the case in which both are zero. In that case, `{S ≥ 0}` has probability one, so the strict-event variant is required. The Cramér-transform bound `ψ*_S(t) ≥ (v/c²) h₁(ct/v)` is outside the formalization. The square-root tail is instead derived directly from Chernoff's inequality at `λ = s/(v + cs)`, where `s = √(2vt)`, in the positive-`v` case.

Corollary 2.11 has the event `{S ≥ t}` for `t > 0` and the bound `exp(-t²/(2(v + ct)))`. The Lean proof uses Chernoff's inequality at `λ = t/(v + ct)` when `v > 0`; the reference derives the result through `h₁(u) ≥ u²/(2(1 + u))`. This parameter choice yields the stated rational bound and need not minimize the Chernoff expression. When `v = c = 0`, Lean's convention `x / 0 = 0` gives a displayed bound of one.

For display (2.10) and the remark after Corollary 2.11, the reference sets `v = Σ E Xᵢ²`, whereas the Lean result permits any upper bound on this quantity. The bounded form assumes `b ≥ 0`, finite second moments, and `Xᵢ ≤ b` almost surely; Theorem 2.9 in the reference assumes `b > 0`. The inequalities `(x₊)^q ≤ b^(q-2) x²` and `2 · 3^(q-2) ≤ q!` establish the moment condition with `c = b/3`. The two-sided, product-measure, and empirical-mean results are derived corollaries of these statements. The empirical-mean theorem uses a strict event, and `bernstein_iid_mean_ge` gives the non-strict event when `B > 0`.

### Degenerate cases

Under the moment assumptions, `v = 0` implies that each `Xᵢ` is zero almost surely, so the centered sum is also zero almost surely. The lemma `General.sum_ae_eq_zero` establishes this conclusion, which is used directly in the tail proofs. The general statements permit `c = 0`, and the bounded statements permit `b = 0`. The non-strict square-root forms require `0 < v ∨ 0 < c`, or `0 < v ∨ 0 < b` in the bounded case; the strict forms permit both parameters to be zero.

Each tail bound assumes `t > 0`. An empty index type gives `S = 0` and is permitted under the stated assumptions. The two-sided bounded forms assume `b ≥ 0`; for a nonempty index type, this also follows from `|Xᵢ| ≤ b`.

The empirical-mean statements require `n > 0`. At `n = 0`, Lean's division convention makes the strict deviation event `{|∫ f| > 0}`, which can have probability one. The bound `B ≥ 0` follows from the almost-sure inequalities `0 ≤ f ≤ B`. The strict empirical-mean result therefore permits `B = 0`, while its non-strict counterpart requires `B > 0`.

## Proof structure

The proof begins with a bound on the exponential series. For `u ≤ 0`, `eᵘ ≤ 1 + u + u²/2`; for general real `x`, the remaining terms can be bounded using its positive part. The identity `Σ_{k≥0} x^(k+3)/(k+3)! = eˣ - 1 - x - x²/2` yields `eˣ ≤ 1 + x + x²/2 + Σ_{k≥0} (x₊)^(k+3)/(k+3)!`.

For a single summand, the resulting expectation bound is `E e^{λY} ≤ 1 + λ E Y + λ²/2 E Y² + Σ_k λ^(k+3) E (Y₊)^(k+3)/(k+3)!`. The proof establishes integrability of `e^{λY}` under summability of the weighted moment series. The interchange of expectation and summation uses `integral_tsum_of_summable_integral_norm`, and `lintegral_tsum` establishes integrability of the series. Under the moment conditions, geometric domination supplies the required summability.

The inequality `log u ≤ u - 1`, together with independence, then gives the CGF bound for the centered sum. The factorization uses mathlib's `iIndepFun.cgf_sum₀`, and the remaining geometric series satisfies `Σ_{q≥2} λ^q c^(q-2) = λ²/(1 - cλ)`. The resulting exponential integrability and CGF bound establish `HasBernsteinCGF`. Chernoff's inequality at the parameter choices above yields the tail bounds for `v > 0`; almost-sure equality to zero establishes the remaining cases.

For bounded summands, the inequalities `(x₊)^q ≤ b^(q-2) x²` and `2 · 3^k ≤ (k+2)!` imply the moment conditions with `c = b/3`. Applying the one-sided bounds to both signs yields the two-sided results. Independence of product coordinates, established by `iIndepFun_pi`, and their measure-preserving projections then yield the product-measure forms. Rescaling the sum yields the empirical-mean and frequency corollaries, while applying the bounded theorem after centering yields the variance corollaries.

### Source organization

| Module | Contents |
| --- | --- |
| `BernsteinLean/Analytic.lean` | Exponential remainder and factorial inequalities. |
| `BernsteinLean/MGF.lean` | Exponential integrability and the CGF bound under moment conditions. |
| `BernsteinLean/CGF.lean` | The `HasBernsteinCGF` condition and its tail inequalities. |
| `BernsteinLean/General.lean` | Tail bounds under the moment conditions, including zero-parameter cases. |
| `BernsteinLean/Bounded.lean` | Derivation of the moment conditions from an almost-sure upper bound. |
| `BernsteinLean/Product.lean` | Independence, integrals, moments, and almost-sure bounds for product coordinates. |
| `BernsteinLean/Statement.lean` | Moment-condition, bounded, two-sided, product-measure, and empirical-mean statements. |
| `BernsteinLean/Variance.lean` | Concentration bounds expressed through the sum of variances. |
| `BernsteinLean/Frequency.lean` | The empirical-frequency corollary. |
| `BernsteinLean/Examples.lean` and `BernsteinLean/BoundaryTests.lean` | Applications to indicators and bounded variables, empty families, zero parameters, and counterexamples showing why certain positivity assumptions are needed. |

The test target `BernsteinLeanTest` builds the examples and boundary checks separately from the main library import.

## Build and verification

The build requires [elan](https://github.com/leanprover/elan), Git, and Python 3.11+ for the verification script. The Lean version is specified in `lean-toolchain` as `leanprover/lean4:v4.35.0`. The mathlib version is fixed at `v4.35.0` in `lakefile.toml` and `lake-manifest.json`.

```bash
lake exe cache get   # download prebuilt mathlib artifacts; do not build mathlib from source
python3 scripts/verify.py  # warning-free build, tests, statements, axioms, premises, proof edges
```

The verification command builds the library and test target with warnings treated as errors. It checks the 18 original public theorem types by definitional equality, compares compiled and freshly elaborated declarations, and records their hypotheses and direct proof dependencies. Axiom checks permit `propext`, `Classical.choice`, and `Quot.sound` and reject additional axioms. The library contains no `sorry`, `admit`, or `native_decide`.

The script checks the reviewed hypothesis classifications, definition context, and required theorem dependencies. Its failure tests include incomplete records, changed statements, missing classifications, and a Lean declaration with a custom axiom. Generated records are written to `.lake/verification/`, and the GitHub Actions workflow runs the same command and retains those records. The script uses the Python standard library and performs no dependency downloads or updates.

[VERIFICATION.md](VERIFICATION.md) describes the checks and their scope. For an intended mathematical change, `--inventory-only` generates the revised declarations for review before the recorded classifications and definition context are updated. The option `--skip-build` is available for development; its result is distinguished from a complete release check. [UPSTREAM.md](UPSTREAM.md) describes a proposed sequence for mathlib review.

## Use in another Lean project

A project using the same mathlib version can declare the dependency as follows, replacing the repository URL and commit with those of the desired revision:

```toml
[[require]]
name = "bernstein"
git = "<repository URL>"
rev = "<commit>"
```

The library is then available through `import BernsteinLean`.

## License

Released under the MIT License, Copyright (c) 2026 Jared Huling. See `LICENSE`.

## Acknowledgment

The Lean proof was developed by Opus 5.5 and double-checked by Astra and Jared Huling.
