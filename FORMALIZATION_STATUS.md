# Formalization status

Canonical manuscript: `xz_mathieu_su2_counterexamples.tex` (arXiv v1).
Initial repository commit: `b4b44eaa8e1804799c9ccc777b2b68f76d5e32c5`.
Canonical manuscript Git blob: `049c436d66548845bf9ba7339548d079bf4c598f`.

Release status: **IN PROGRESS**. Core proofs are implemented; final clean validation and supporting extensions remain.
Lean: `v4.34.0`; mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
The five central named results and all substantive labelled equations are inventoried below.
PROVED means the full stated claim is kernel-checked without project axioms.
The dependency graph describes logical obligations; supporting implementation lemmas may use alternate acyclic routes.

### `def:xz`

- Statement: Admissible Laurent polynomials with polynomial interval coefficients, exact torus spectrum, convex hull, and the xz implication.
- Status: **PROVED**.
- Core release gate: no.
- Lean correspondence: `Laurent, XZConjecture`.
- Module: `LaurentIntegral`.
- Dependencies: none.
- Proof route / representation: LaurentPolynomial over ℂ[X]; torus exponents are integer coefficients; convex hull is taken in ℝ.
- Blocker: none identified.

### `def:mathieu`

- Statement: Mathieu–Zhao subspaces: all positive pure powers in the subspace imply eventual membership of every fixed multiple.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `IsMathieuSubspace, not_isMathieuSubspace_of_witness`.
- Module: `Basic`.
- Dependencies: none.
- Proof route / representation: The usual eventual positive-power condition on a complex submodule.
- Blocker: none identified.

### `eq:I-def`

- Statement: Actual interval integral of the constant term equals interval times normalized circle Haar integration.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `integral_eq_interval_circle, circle_constantTerm`.
- Module: `CircleIntegral`.
- Dependencies: `def:xz`.
- Proof route / representation: Character cancellation under genuine normalized circle Haar measure proves constant-term equivalence for every Laurent polynomial.
- Blocker: none identified.

### `eq:beta-binomial-intro`

- Statement: For 0 ≤ k ≤ n, choose(n,k) ∫₀¹ x^k(1-x)^(n-k) dx = 1/(n+1).
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `bernstein_integral`.
- Module: `Bernstein`.
- Dependencies: none.
- Proof route / representation: Complex beta/Gamma evaluation and exact factorial cancellation.
- Blocker: none identified.

### `eq:bernstein-average`

- Statement: Coefficientwise integral of ((1-x)+xz)^n is (Σ k=0..n z^k)/(n+1).
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `bernstein_average, xzFamily_integrated_coeff`.
- Module: `Bernstein`.
- Dependencies: `eq:beta-binomial-intro`.
- Proof route / representation: Finite binomial expansion and interval integration; coefficientwise telescoping also proved.
- Blocker: none identified.

### `eq:basic-f`

- Statement: f=(1-z⁻¹)((1-x)+xz)=xz+(1-2x)-(1-x)z⁻¹.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `basic, basic_expansion`.
- Module: `XZWitness`.
- Dependencies: `def:xz`.
- Proof route / representation: Literal polynomial-coefficient Laurent expression; expansion is a ring equality.
- Blocker: none identified.

### `basic-spectrum`

- Statement: The coefficient-polynomial spectrum of f is exactly {-1,0,1}; zero belongs to its real convex hull.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `basic_spectrum, basic_zero_mem_convexHull`.
- Module: `XZWitness`.
- Dependencies: `eq:basic-f`.
- Proof route / representation: Nonzero coefficient polynomials at exactly -1,0,1; zero already lies in the spectrum.
- Blocker: none identified.

### `alternating-sums`

- Statement: The full positive binomial row sums to zero; the row omitting its last term sums to (-1)^(n-1).
- Status: **TODO**.
- Core release gate: no.
- Lean correspondence: `pending`.
- Module: `Bernstein`.
- Dependencies: none.
- Proof route / representation: To be implemented faithfully; Laurent coefficient polynomials and actual Haar measures.
- Blocker: none identified.

### `eq:basic-moments`

- Statement: For every n ≥ 1, I(f^n)=0 and I(z⁻¹f^n)=(-1)^(n-1)/(n+1) ≠ 0.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `basic_pure, basic_marked, basic_marked_ne_zero`.
- Module: `XZWitness`.
- Dependencies: `eq:I-def`, `eq:bernstein-average`, `eq:basic-f`.
- Proof route / representation: Bernstein integration and geometric-sum telescoping; arbitrary positive natural exponent.
- Blocker: none identified.

### `thm:basic-xz`

- Statement: Theorem 2.1: exact basic moments, failure of xz(1,1), and failure of the Mathieu–Zhao property for ker I.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `basic_xz`.
- Module: `XZWitness`.
- Dependencies: `eq:basic-moments`, `basic-spectrum`, `def:mathieu`.
- Proof route / representation: Literal moments, spectrum, xz failure, and kernel Mathieu–Zhao failure.
- Blocker: none identified.

### `cor:all-mixed-xz`

- Statement: Corollary 2.2: all k,l ≥ 1 fail the xz conjecture and the product-integration kernel Mathieu–Zhao property.
- Status: **TODO**.
- Core release gate: no.
- Lean correspondence: `pending`.
- Module: `Padding`.
- Dependencies: `thm:basic-xz`.
- Proof route / representation: To be implemented faithfully; Laurent coefficient polynomials and actual Haar measures.
- Blocker: none identified.

### `rem:generating`

- Statement: Remark 2.3: trinomial constant-term resolvent equals inverse square root; radicand simplifies to (1-t)^2+4tx; integrated series is one.
- Status: **TODO**.
- Core release gate: no.
- Lean correspondence: `pending`.
- Module: `GeneratingFunction`.
- Dependencies: `eq:basic-moments`.
- Proof route / representation: To be implemented faithfully; Laurent coefficient polynomials and actual Haar measures.
- Blocker: none identified.

### `eq:family`

- Statement: For integer d ≥ 1 and nonzero complex λ,μ, f=λ(1-μz^(-d))((1-x)+xμ⁻¹z^d), with exact expanded coefficients.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `circuit, circuit_expansion, circuit_eq_map`.
- Module: `CircuitFamily`.
- Dependencies: `eq:basic-f`.
- Proof route / representation: Exact substitution z ↦ μ⁻¹z^d is a proved ring homomorphism.
- Blocker: none identified.

### `family-spectrum`

- Statement: Spectrum of f(d,λ,μ) is exactly {-d,0,d}.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `circuit_spectrum`.
- Module: `CircuitFamily`.
- Dependencies: `eq:family`.
- Proof route / representation: Exact polynomial support with d an integer ≥1 and both parameters nonzero.
- Blocker: none identified.

### `eq:family-pure`

- Statement: For all n ≥ 1, I(f(d,λ,μ)^n)=0.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `circuit_pure`.
- Module: `CircuitFamily`.
- Dependencies: `eq:family`, `eq:basic-moments`.
- Proof route / representation: Coefficient-preserving substitution and scalar multiplication reduce to the basic moment.
- Blocker: none identified.

### `eq:family-mixed`

- Statement: For all n ≥ 1, I(z^(-d)f(d,λ,μ)^n)=(-1)^(n-1)λ^nμ⁻¹/(n+1) ≠ 0.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `circuit_marked, circuit_marked_ne_zero`.
- Module: `CircuitFamily`.
- Dependencies: `eq:family`, `eq:basic-moments`.
- Proof route / representation: Exact marked coefficient scaling μ⁻¹, scalar factor lam^n, and nonvanishing.
- Blocker: none identified.

### `prop:family`

- Statement: Proposition 3.1 in its full integer d ≥ 1, nonzero complex λ,μ generality.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `circuit_family`.
- Module: `CircuitFamily`.
- Dependencies: `family-spectrum`, `eq:family-pure`, `eq:family-mixed`.
- Proof route / representation: All three parameters and the exact support and moment conclusions.
- Blocker: none identified.

### `su2-coordinates`

- Statement: Actual determinant-one unitary 2×2 matrices: c=-conj(b), d=conj(a), ad-bc=1; polynomial entries are representative functions.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `Hopf.su2_entries, Hopf.su2_determinant_relation, Hopf.su2Entry, representative_eq_span_coefficients`.
- Module: `SU2Basic`.
- Dependencies: none.
- Proof route / representation: Actual mathlib determinant-one unitary matrices; finite spans of continuous representation coefficients.
- Blocker: none identified.

### `eq:beta-map`

- Statement: β(z₁,z₂,x)=((1-x)z₂,xz₁,-z₁⁻¹,z₂⁻¹); its polynomial evaluation is defined.
- Status: **TODO**.
- Core release gate: no.
- Lean correspondence: `pending`.
- Module: `SU2Integration`.
- Dependencies: `su2-coordinates`.
- Proof route / representation: To be implemented faithfully; Laurent coefficient polynomials and actual Haar measures.
- Blocker: none identified.

### `eq:su2-monomial`

- Statement: Normalized Haar integral of a^r b^s c^t d^u is (-1)^s δ(r,u)δ(s,t) r!s!/(r+s+1)!.
- Status: **PARTIAL**.
- Core release gate: no.
- Lean correspondence: `Hopf.su2_polynomial_transfer, Hopf.balanced_entry_integral`.
- Module: `SU2Integration`.
- Dependencies: `su2-coordinates`, `eq:beta-binomial-intro`.
- Proof route / representation: Proved for every polynomial in ad,b,c and for monomials with r=u. The full arbitrary-polynomial statement is still pending; it is not assumed in Theorem 4.2.
- Blocker: none identified.

### `eq:su2-integration`

- Statement: For every P ∈ ℂ[a,b,c,d], actual normalized Haar integral equals interval and two-circle normalized Haar integral of P∘β.
- Status: **PARTIAL**.
- Core release gate: no.
- Lean correspondence: `Hopf.su2_polynomial_transfer, Hopf.balanced_entry_integral`.
- Module: `SU2Integration`.
- Dependencies: `eq:su2-monomial`, `eq:beta-map`, `eq:I-def`.
- Proof route / representation: Proved for every polynomial in ad,b,c and for monomials with r=u. The full arbitrary-polynomial statement is still pending; it is not assumed in Theorem 4.2.
- Blocker: none identified.

### `lem:su2-integration`

- Statement: Lemma 4.1: full arbitrary-polynomial integration formula, by monomial identities and linearity.
- Status: **PARTIAL**.
- Core release gate: no.
- Lean correspondence: `Hopf.su2_polynomial_transfer, Hopf.balanced_entry_integral`.
- Module: `SU2Integration`.
- Dependencies: `eq:su2-integration`.
- Proof route / representation: Proved for every polynomial in ad,b,c and for monomials with r=u. The full arbitrary-polynomial statement is still pending; it is not assumed in Theorem 4.2.
- Blocker: none identified.

### `eq:FG-family`

- Statement: Actual entry representative functions F=λ(1+μc)(ad+μ⁻¹b), G=-c, and exact beta substitution.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `Hopf.su2F_apply, Hopf.su2G_apply, Hopf.betaTriple_F, Hopf.betaTriple_G`.
- Module: `SU2Counterexample`.
- Dependencies: `su2-coordinates`, `eq:family`.
- Proof route / representation: Entry-polynomial definitions and exact beta substitution, with the manuscript matrix layout [a,c;b,d].
- Blocker: none identified.

### `eq:su2-pure`

- Statement: For all n ≥ 1, actual normalized Haar integral of F^n is zero.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `Hopf.su2_pure, Hopf.su2_counterexample`.
- Module: `SU2Counterexample`.
- Dependencies: `eq:FG-family`.
- Proof route / representation: Normalized-Haar transfer for every polynomial in ad,b,c, proved from sphere moment recurrence.
- Blocker: none identified.

### `eq:su2-mixed`

- Statement: For all n ≥ 1, actual normalized Haar integral of F^nG is (-1)^(n-1)λ^nμ⁻¹/(n+1) ≠ 0.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `Hopf.su2_marked, Hopf.su2_marked_ne_zero, Hopf.su2_counterexample`.
- Module: `SU2Counterexample`.
- Dependencies: `eq:FG-family`.
- Proof route / representation: Same transfer applies to all marked powers; explicit actual Haar integral wrapper.
- Blocker: none identified.

### `thm:su2`

- Statement: Theorem 4.2: the exact parametric moments and failure of the actual representative-algebra Mathieu property on SU(2).
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `Hopf.su2_counterexample, Hopf.SU2_not_mathieu`.
- Module: `SU2Counterexample`.
- Dependencies: `eq:su2-pure`, `eq:su2-mixed`, `def:mathieu`.
- Proof route / representation: Exact parametric Haar moments and actual representative-algebra Mathieu failure.
- Blocker: none identified.

### `small-pair`

- Statement: The exact λ=μ=1 pair F=(1+c)(ad+b), G=-c and its moments.
- Status: **PROVED**.
- Core release gate: yes.
- Lean correspondence: `Hopf.small_pair`.
- Module: `SU2Counterexample`.
- Dependencies: `thm:su2`.
- Proof route / representation: Specialization lam=μ=1 of the exact theorem.
- Blocker: none identified.

### `section5:cancellation`

- Statement: Bernstein equal weights, geometric sum, full-row cancellation, and persistent marked moments.
- Status: **TODO**.
- Core release gate: no.
- Lean correspondence: `pending`.
- Module: `Bernstein`.
- Dependencies: `eq:bernstein-average`, `alternating-sums`, `eq:basic-moments`.
- Proof route / representation: To be implemented faithfully; Laurent coefficient polynomials and actual Haar measures.
- Blocker: none identified.

### `rem:one-way-jacobian`

- Statement: Remark 4.3: the one-way implication does not yield the two-dimensional Jacobian conjecture from the SU(2) counterexample.
- Status: **EXPOSITORY**.
- Core release gate: no.
- Lean correspondence: `pending`.
- Module: `none`.
- Dependencies: none.
- Proof route / representation: To be implemented faithfully; Laurent coefficient polynomials and actual Haar measures.
- Blocker: none identified.

### `eq:xz-conjecture`

- Statement: The displayed xz implication and its exact failure on the witness.
- Status: **PROVED**.
- Core release gate: no.
- Lean correspondence: `XZConjecture, not_XZConjecture`.
- Module: `XZWitness`.
- Dependencies: `def:xz`, `thm:basic-xz`.
- Proof route / representation: Literal interval/constant-term functional with proved circle Haar equivalence.
- Blocker: none identified.

