# Preparation for mathlib review

The library proves Bernstein's inequality using mathlib as its only external mathematical dependency. It is released under the MIT License, and its file headers and public imports follow the Lean module system used by the specified toolchain. The following sequence is a proposal for review; no upstream submission or discussion has been initiated.

## Existing formalizations

Before preparing a submission, compare the proposed declarations with [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) and current mathlib. The scalar results in `SLT/SubGaussian.lean` derive tails from a local quadratic CGF condition, while `SLT/RMT/MatBern.lean` develops Bernstein's inequality for bounded matrix summands. The [README](README.md#related-formalizations) records the reviewed revision and the relation to this library.

A release can provide a reusable scalar development from the Boucheron, Lugosi and Massart moment conditions. It should acknowledge the existing Bernstein formalizations and describe the additional assumptions, conclusions, and interfaces precisely. A mathlib proposal should identify reusable arguments and overlapping declarations before introducing another concentration interface. Coordination with the existing authors and mathlib maintainers would help determine which results to contribute and which interfaces to share.

## Proposed review sequence

1. Compare the exponential remainder and factorial lemmas in `Analytic.lean` with existing mathlib results and determine suitable namespaces. These lemmas can be reviewed independently of the probability results.
2. Review the exponential-integrability argument for a single variable and the CGF bound for the independent sum. The summability and integrability assumptions are needed to justify the expectation and series calculations.
3. Discuss the representation of one-sided sub-gamma CGF bounds with maintainers. The local predicate `HasBernsteinCGF` includes exponential integrability and the bound for each positive `λ` satisfying `cλ < 1`. Its two closed-form tail methods require `v > 0`; extending those methods to `v = 0` would be additional work. The moment-condition theorems already cover that case through the almost-sure-zero argument.
4. Determine the placement of the moment-condition and bounded-summand results within `ProbabilityTheory`. The statements should retain the distinction between raw second moments and variances of centered variables, the factor of one third, and the conditions needed for strict and non-strict events when parameters are zero.
5. Review the product-measure, empirical-mean, variance, and frequency corollaries after the general statements and naming conventions have been agreed. Examples and repository-specific regression checks can remain separate from the main library import.

## Statement preservation and submission

The checks in `verification/OriginalStatements.lean` compare the current results with the 18 original public theorem types. Changes to namespaces or theorem arguments for a mathlib submission would require updates to projects that use the library and a new comparison of the statements.

A submission should include an explanation of the proof, a review of its assumptions, and disclosure of AI assistance under the contribution requirements in effect at submission. The local verification records document the checks performed on this implementation and can support the maintainers' mathematical and software review.
