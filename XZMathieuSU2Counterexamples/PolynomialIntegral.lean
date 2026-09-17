import XZMathieuSU2Counterexamples.SU2Orbit
import Mathlib.Algebra.Polynomial.Roots

/-! Coefficientwise integration of polynomials with continuous sphere-function coefficients. -/

noncomputable section
open MeasureTheory Polynomial
namespace XZMathieuSU2Counterexamples.Hopf

def integrateCoefficients (p : Polynomial C(Sphere, ℂ)) : Polynomial ℂ :=
  ∑ n ∈ p.support, monomial n (∫ z, p.coeff n z ∂surfaceMeasure)

theorem integrateCoefficients_coeff (p : Polynomial C(Sphere, ℂ)) (n : ℕ) :
    (integrateCoefficients p).coeff n = ∫ z, p.coeff n z ∂surfaceMeasure := by
  classical
  simp only [integrateCoefficients, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [notMem_support_iff.mp h]

theorem integrateCoefficients_eval (p : Polynomial C(Sphere, ℂ)) (c : ℂ) :
    (integrateCoefficients p).eval c =
      ∫ z, (p.eval (ContinuousMap.const Sphere c)) z ∂surfaceMeasure := by
  classical
  simp only [integrateCoefficients, eval_finsetSum, eval_monomial]
  conv_rhs => rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum]
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
    ContinuousMap.const_apply]
  rw [integral_finsetSum]
  · congr 1
    ext n
    rw [integral_mul_const]
  · intro n hn
    exact ((p.coeff n).continuous.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem integrateCoefficients_eq_zero (p : Polynomial C(Sphere, ℂ))
    (h : ∀ t : ℝ, (∫ z, (p.eval (ContinuousMap.const Sphere (t : ℂ))) z ∂surfaceMeasure) = 0) :
    integrateCoefficients p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro _ ⟨t, rfl⟩
  exact (integrateCoefficients_eval p t).trans (h t)

end XZMathieuSU2Counterexamples.Hopf

/- Adapted from MathieuProperty/PolynomialIntegral.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
