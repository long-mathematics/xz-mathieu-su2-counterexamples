# Formalization audit

Audit date: 2026-09-17. Release classification: **audited core-complete formalization**.
All five central named results are proved. Two supporting derivations remain explicitly
partial; this is not a claim of full-paper coverage.

## Independent source review

After implementing the proofs, the entire canonical manuscript was reread independently
of the working ledger, and its statements, displayed formulas, proof arguments, and
parameter ranges were compared with the Lean definitions and theorem signatures.
The Laurent witness, circuit family, finite-product padding, actual SU(2) functions,
Haar measures, and full four-variable integration formula were inspected directly.
No mathematical discrepancy requiring a manuscript correction was found.

The canonical source is `xz_mathieu_su2_counterexamples.tex`, Git blob
`049c436d66548845bf9ba7339548d079bf4c598f`, recorded at initial commit
`b4b44eaa8e1804799c9ccc777b2b68f76d5e32c5`.
The manuscript, PDF, original Python verifier and its recorded output, CITATION.cff,
and LICENSE are unchanged from that commit. No LaTeX rebuild was needed because
neither the verified source nor its PDF changed.

## Named-result correspondence

All declarations below are in the `XZMathieuSU2Counterexamples` namespace.

| Manuscript result | Main Lean correspondence | Review conclusion |
| --- | --- | --- |
| Theorem 2.1 (`thm:basic-xz`) | `basic_xz`, `basic_spectrum`, `basic_zero_mem_convexHull` | Literal Laurent witness, exact positive pure and marked moments, spectrum, xz failure, and Mathieu–Zhao kernel failure. |
| Corollary 2.2 (`cor:all-mixed-xz`) | `all_mixed_xz`, `pad_integral`, `pad_eval`, `multiIntegral_eq_product` | Every finite pair k,l ≥ 1; polynomial padding, product-integral correspondence, and both failure consequences. |
| Proposition 3.1 (`prop:family`) | `circuit_family`, `circuit_expansion` | Integer d ≥ 1 and arbitrary nonzero complex lam and μ; exact three-point spectrum and both moments. |
| Lemma 4.1 (`lem:su2-integration`) | `Hopf.su2_monomial`, `Hopf.su2_integration_formula` | Both Kronecker conditions and the factorial monomial formula; full arbitrary four-variable polynomial equality of actual integrals. |
| Theorem 4.2 (`thm:su2`) | `Hopf.su2_counterexample`, `Hopf.SU2_not_mathieu`, `Hopf.small_pair` | Actual SU(2), normalized Haar, the full complex parameter family, every positive exponent, nonvanishing, and failure in the representative-function algebra. |

The manuscript matrix convention is `[a,c;b,d]`: a and b form the first column.
The Lean entry functions and beta substitution respect this convention. In particular,
F = lam(1 + μc)(ad + μ⁻¹b), G = -c, and the marked moment is exactly
(-1)^(n-1) lam^n μ⁻¹/(n+1). The exposed small pair sets both parameters to one.

## Representations and proof routes

* `LaurentPolynomial ℂ[X]` retains coefficient polynomials and integer exponents.
  `integral` is actual interval integration of the constant coefficient.
  `integral_eq_interval_circle` proves equality with normalized circle Haar
  integration for every Laurent polynomial. The beta/Bernstein calculation uses
  exact beta/Gamma and factorial identities, with no finite-exponent bound.
* Finite products use `AddMonoidAlgebra (MvPolynomial (Fin l) ℂ) (Fin k → ℤ)`.
  The cube is the product of restricted interval probability measures; the torus
  is the product of normalized circle Haar measures, proved equal to normalized
  Haar on the product group. Padding preserves evaluation and reduces the actual
  integral to the first coordinates. Support and the convex-hull obstruction are
  proved in this representation.
* `SU2` is mathlib's `Matrix.specialUnitaryGroup (Fin 2) ℂ`.
  `normalizedHaar` is actual Haar measure normalized on the whole compact group.
  Representative functions are finite spans of continuous finite-dimensional
  matrix coefficients; their algebra closure and the usual representation
  coefficient correspondence are proved. Coordinate functions belong to this algebra.
* The first-column homeomorphism transports Haar to normalized Euclidean sphere
  measure. Orthogonal invariance and a rotation recurrence give sphere factorial
  moments. Left and right phases give both vanishing conditions for general SU(2)
  entry monomials. This is an alternate proof of the manuscript monomial formula.
* Theorem 4.2 uses a proved transfer for all polynomials in ad,b,c. Its proof does
  not depend on the later full four-variable lemma. Independently,
  `su2_integration_formula` extends the full monomial equality by polynomial
  linearity, including continuity and integrability obligations on the interval
  and both actual circles. Neither transfer assumes a polar-coordinate law.

Related infrastructure was adapted from the MIT-licensed
`long-mathematics/mathieu-property-compact-connected-lie-groups` reference commit
`d7199cfcc342b3e0c332982740d1f3beecf01ab8`; applicable source notices were retained.
Only the machinery needed here was included. There is no build-time dependency
on that repository; mathlib is the only direct external Lean dependency.

## Remaining supporting coverage

The ledger has 32 entries: 28 PROVED, two PARTIAL, and two EXPOSITORY.
All core release gates and all five named results are PROVED.

* `rem:generating` (Remark 2.3): the formal moment series equals one and the
  radicand simplification is proved. The general Laurent-trinomial constant-term
  inverse-square-root identity and its analytic square-root integral derivation
  remain absent. The pinned power-series library was searched; no ready theorem
  supplied the required formal binomial series and analytic branch infrastructure.
  These optional derivations are not used by the counterexample proofs.
* `su2-polar-description`: the separate joint square-root polar-coordinate
  pushforward law in the proof of Lemma 4.1 is not proved as a measure equality.
  First-column sphere transport and all polynomial monomial moments are proved.
  The full statement of Lemma 4.1 is proved through the recurrence route above,
  so this supporting description is not a missing premise or a weakened lemma.
* `rem:one-way-jacobian` and `context:external-results` are expository context.
  No cited background assertion has been introduced as a project axiom.

Section 5's cancellation mechanism, full and partial alternating-binomial sums,
expansions, spectra, parameter nonvanishing, and all proof-critical bridges are proved.

## Validation and proof integrity

Pinned versions: Lean `v4.34.0`; mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

* Dependency cache fetch succeeded without changing the pinned configuration.
* A fresh project rebuild after `lake clean xz_mathieu_su2_counterexamples`
  succeeded: 3,599 build jobs, 27.83 seconds locally. Dependency artifacts were
  cached; every project proof was rebuilt by Lean. A subsequent rebuild after
  comment-only cleanup also succeeded.
* `python3 scripts/audit_source.py` passed: 27 owned Lean files, including the
  audit executable; 26 library modules in the root import closure (25 substantive
  modules plus the root); 32 ledger entries; all five named manuscript results.
  It checks forbidden source escapes, reachability, all manuscript labels,
  required core gates, correspondence names, acyclic dependencies, canonical
  source identity, and consistency of README completion claims.
* `python3 scripts/test_audit_source.py` passed all 11 mutation checks, including
  deliberately broken coverage, proof-integrity, source-identity, and release claims.
* `lake env lean scripts/audit_lean.lean` passed across **575 namespace declarations,
  including 466 theorem constants**. Every collected transitive axiom is one of
  `propext`, `Classical.choice`, and `Quot.sound`. The audit also checks the required
  release declarations are theorem constants in the loaded environment.
* The original `scripts/verify_xz_mathieu_counterexamples.py` passed its independent
  exact rational/integer checks. These finite checks are corroboration, not substitutes
  for the universally quantified Lean proofs.
* `git diff --check` passed. Generated artifacts and dependency caches are ignored.

The GitHub workflow **Build and audit Lean** repeats source and mutation audits,
installs the pinned toolchain, fetches only pinned dependency artifacts, compiles all
project proofs, audits transitive axioms, and runs the original Python verifier.
It uses pinned action SHAs and read-only repository permissions. Release merging
requires this workflow to succeed; the post-merge main run is also verified.
