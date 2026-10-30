# Verification of the Bernstein library

The command `python3 scripts/verify.py` builds the library and checks its declarations, hypotheses, and proof dependencies. The mathematical reference is Boucheron, Lugosi and Massart (2013), *Concentration Inequalities*, Section 2.8: the CGF and tail clauses of Theorem 2.10, Corollary 2.11, display (2.10), and the bounded-case remark. The Cramér-transform clause is outside the formalization. The reference was compared with the complete Lean statements during the October 30, 2026 review.

## Verification scope

| Check | Scope |
| --- | --- |
| Compilation and axioms | The library and test target are built with warnings treated as errors. The 64 named declarations, including private helpers and named tests, are checked through compiled imports and freshly elaborated source. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. |
| Parameters and hypotheses | `.lake/verification/declarations.json` records the full elaborated types, their 732 binders and binder kinds, the 292 proposition binders, and the conclusions. |
| Sources of hypotheses | `verification/reviewed_statements.json` records the mathematical source of each proposition binder. It distinguishes reference assumptions from conditions introduced for the formalization or derived corollaries. Changed statements and incomplete classifications fail verification. |
| Proof dependencies | The source check records direct theorem dependencies and compares them with `verification/proof_edges.json`. These include the exponential-series bound, summability, exponential integrability, independence factorization, CGF and tail calculations, the bounded-moment argument, the union bound, and the product-measure and empirical-mean derivations. |
| Statement preservation | `verification/OriginalStatements.lean` checks definitional equality with the 18 original public theorem types. The variance and frequency corollaries are derived extensions. The definition of `HasBernsteinCGF` is included in the reviewed source context. |

The checks apply to the source files and dependency versions identified by the hashes from a successful run. Each declaration is verified under its recorded hypotheses. The automated checks establish agreement with the reviewed statements and classifications; the correspondence with the reference theorem also requires mathematical review of the definitions and assumptions. Acceptance into mathlib requires a separate review by its maintainers.

## Moment assumptions and derived results

In the original theorem, `v` bounds the sum of raw second moments. The variance corollaries apply the bounded theorem to centered variables, for which the second moments equal the variances. Their bound on each summand therefore applies to `Xᵢ - E Xᵢ`. The frequency corollary follows from the identity `E(1_A²) = μ(A)` and uses this raw second moment in its threshold.

The lemma `MGF.single` requires summability of a weighted series of positive-part moments. Finite moments alone are insufficient to establish a finite moment generating function. Under the theorem's moment conditions, `MGF.cgf_le` establishes summability by geometric domination. The independent-sum integrability lemma requires integrability of each coordinate exponential, which is established in the proof that applies it.

The predicate `HasBernsteinCGF` includes exponential integrability and the CGF bound explicitly. Its two closed-form tail methods require `v > 0`. The moment-condition theorems in `General` also cover `v = 0`, because their assumptions then imply that the summands vanish almost surely.

The examples and boundary tests cover empty families, zero tail probabilities at positive thresholds, a zero bound on the summands, and the case `c = 0` without a lower bound on the variables. They also include counterexamples showing why a non-strict zero threshold and a zero sample size require separate treatment. The command `lake test` builds these tests; the main library import includes the mathematical results separately.

## Running the checks

After installing elan and obtaining the mathlib cache for the version specified in the dependency manifest, run the following commands from the project root:

```sh
lake exe cache get
python3 scripts/verify.py
```

The script checks compilation, declaration records, axioms, theorem signatures, reviewed definitions, hypothesis classifications, and the required direct proof dependencies. It also compares the dependency revisions with `lake-manifest.json` and checks for modifications to tracked dependency sources. Cached mathlib results are checked through Lean's kernel and their transitive axiom dependencies; the script does not rebuild mathlib from source or download dependencies.

The 13 Python tests in `scripts/test_verify.py` check rejection of invalid or incomplete verification records, unsupported declarations, changed types, and missing hypothesis classifications. A separate Lean check introduces a custom axiom and must fail with the specified rejection message. An unrelated compilation error does not satisfy that check.

## Verification records and maintenance

Generated Lean files, logs, declaration inventories, source hashes, dependency revisions, and `result.json` are written to `.lake/verification/`. A complete release check reports `status: pass` with `build_performed: true`. The script replaces the previous result at the start of each run, so a failed run does not retain an earlier success. The GitHub Actions workflow runs the same command and retains this directory as an artifact.

The options `--inventory-only` and `--skip-build` produce distinct development statuses. After an intended mathematical change, `--inventory-only` generates the revised declarations for comparison with the reference and the previous statements. Updating the review record requires inspection of the assumptions, definitions, and proof dependencies. The script leaves that record unchanged, so the mathematical review remains an explicit step.
