# Counterexamples to the xz-Conjecture and the Mathieu Conjecture for SU(2)

## Abstract

Let

$$
\mathcal{I}(h)=\int_0^1\int_{\mathbb{T}} h(x,z)\,\frac{dz}{2\pi i z}\,dx,
\qquad
h\in\mathbb{C}[x,z,z^{-1}].
$$

We give the three-term Laurent polynomial

$$
f(x,z)=(1-z^{-1})\bigl((1-x)+xz\bigr)
$$

for which

$$
\mathcal{I}(f^n)=0,
\qquad
\mathcal{I}(z^{-1}f^n)=\frac{(-1)^{n-1}}{n+1}\neq 0
\qquad (n\ge 1).
$$

Since $\mathrm{Sp}(f)=\{-1,0,1\}$, this disproves the $xz$-conjecture already with one interval variable and one torus variable, and it also shows that $\ker \mathcal{I}$ is not a Mathieu--Zhao subspace. Padding gives counterexamples to every mixed case of the $xz$-conjecture. Writing the coordinate functions on $SU(2)$ as

$$
g=\begin{pmatrix}
a & c \\
b & d
\end{pmatrix},
$$

the same example lifts, through the integration formula of Müger and Tuset, to the regular functions

$$
F=(1+c)(ad+b),
\qquad
G=-c,
$$

which satisfy

$$
\int_{SU(2)} F^n\,dg=0,
\qquad
\int_{SU(2)} F^nG\,dg=\frac{(-1)^{n-1}}{n+1}\neq 0
$$

for every $n\ge 1$. Thus the Mathieu conjecture for $SU(2)$ is false.

## Preprint and source

- [arXiv:2607.19012](https://arxiv.org/abs/2607.19012)
- [Preprint PDF](xz_mathieu_su2_counterexamples.pdf)
- [LaTeX source](xz_mathieu_su2_counterexamples.tex)
- [Exact verification script](scripts/verify_xz_mathieu_counterexamples.py)
- [Verification output](scripts/verify_xz_mathieu_counterexamples.txt)

The checked-in LaTeX source is the source corresponding to arXiv v1 (July 21, 2026), renamed to follow the repository naming convention. The PDF is compiled from that source.

## Verification

The auxiliary script performs exact rational/integer checks of the beta-binomial identities underlying Theorem 2.1 and Proposition 3.1, together with the monomial identity used in the $SU(2)$ integration formula. Run

```sh
python3 scripts/verify_xz_mathieu_counterexamples.py
```

The script is an independent computational check of the displayed algebraic identities over the stated finite ranges; the proofs in the manuscript are symbolic and valid for all positive exponents.

## Lean formalization

The core counterexample theorems are fully formalized in Lean.
All five central named results are covered: Theorem 2.1, Corollary 2.2 for every
$k,l\geq1$, Proposition 3.1 with its full three-parameter family, the full
arbitrary-polynomial integration formula in Lemma 4.1, and Theorem 4.2 on
actual $SU(2)$ with normalized Haar measure and the representative-function
algebra. The explicit $\lambda=\mu=1$ pair is included.

The formalization uses Lean **4.34.0** and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. No project axioms or proof placeholders
are used. Mathlib is the only external Lean dependency.

- [Root Lean source](XZMathieuSU2Counterexamples.lean)
- [Detailed coverage ledger](FORMALIZATION_STATUS.md)

Remaining supporting claims include **Remark 2.3** (`rem:generating`):
the general Laurent-trinomial inverse-square-root constant-term identity and
its analytic square-root integral derivation. The constant formal moment
series and the radicand simplification are proved. This release therefore
claims core completion, not full-paper coverage.

The separate joint polar-coordinate measure description in the proof of
Lemma 4.1 (`su2-polar-description`) is also not formalized. The full integration
formula itself is proved using phase invariance and a sphere-moment recurrence.

Build and audit with:

```sh
python3 scripts/fetch_mathlib_cache.py
python3 scripts/audit_source.py
lake build
lake env lean scripts/audit_lean.lean
python3 scripts/verify_xz_mathieu_counterexamples.py
```

For a clean rebuild of project proofs, run `lake clean xz_mathieu_su2_counterexamples`
before `lake build`. Dependency caches are not proof substitutes; all project
proofs are compiled by Lean and their transitive axioms are audited.
