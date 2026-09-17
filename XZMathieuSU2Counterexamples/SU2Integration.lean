import XZMathieuSU2Counterexamples.SU2Basic
import XZMathieuSU2Counterexamples.CircuitFamily
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section
open MeasureTheory Polynomial
namespace XZMathieuSU2Counterexamples

theorem beta_factorial (r s : ℕ) :
    (∫ x in (0 : ℝ)..1, (1-(x : ℂ))^r * (x : ℂ)^s) =
      (r.factorial : ℂ) * s.factorial / (r+s+1).factorial := by
  have he : (∫ x in (0 : ℝ)..1, (1-(x : ℂ))^r * (x : ℂ)^s) =
      Complex.betaIntegral (s+1) (r+1 : ℕ) := by
    unfold Complex.betaIntegral
    congr 1
    funext x
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Complex.cpow_natCast]
    ring
  rw [he, Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simp; positivity) (by simp; positivity)]
  have hs : (s+1 : ℂ) + (r+1 : ℕ) = ((r+s+1 : ℕ)+1 : ℂ) := by push_cast; ring
  rw [hs]
  simp only [Complex.Gamma_nat_eq_factorial]
  have hg (n : ℕ) : Complex.Gamma ((n : ℂ)+1) = (n.factorial : ℂ) :=
    Complex.Gamma_nat_eq_factorial n
  simp only [Nat.cast_add, Nat.cast_one, hg]
  ring

namespace Hopf
abbrev TriplePolynomial := MvPolynomial (Fin 3) ℂ

/-- Polynomial in the three regular functions ad, b, c. -/
def entryTriple : TriplePolynomial →ₐ[ℂ] representativeFunctions (G := SU2) :=
  MvPolynomial.aeval ![su2Entry 0 0 * su2Entry 1 1, su2Entry 1 0, su2Entry 0 1]

/-- The exact manuscript beta substitution on ad, b, c. -/
def betaTriple : TriplePolynomial →ₐ[ℂ] Laurent :=
  MvPolynomial.aeval ![LaurentPolynomial.C (1-X),
    LaurentPolynomial.C X * LaurentPolynomial.T 1, -LaurentPolynomial.T (-1)]

theorem entryTriple_monomial (e : Fin 3 →₀ ℕ) (c : ℂ) (g : SU2) :
    (entryTriple (MvPolynomial.monomial e c)).val g =
      c * entryMonomial (e 0) (e 1) (e 2) (e 0) g := by
  simp only [entryTriple, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  change c * ((g.val 0 0 * g.val 1 1)^e 0 *
    (g.val 1 0^e 1 * (g.val 0 1^e 2 * 1))) = _
  simp only [entryMonomial, mul_pow]
  ring

theorem betaTriple_monomial (e : Fin 3 →₀ ℕ) (c : ℂ) :
    betaTriple (MvPolynomial.monomial e c) =
      LaurentPolynomial.C (C (c * (-1)^e 2) * (1-X)^e 0 * X^e 1) *
        LaurentPolynomial.T ((e 1 : ℤ) - e 2) := by
  simp only [betaTriple, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  change LaurentPolynomial.C (C c) * (LaurentPolynomial.C (1-X)^e 0 *
    ((LaurentPolynomial.C X * LaurentPolynomial.T 1)^e 1 *
    ((-LaurentPolynomial.T (-1))^e 2 * 1))) = _
  rw [neg_pow (LaurentPolynomial.T (-1) : Laurent) (e 2)]
  simp only [mul_pow, mul_one, LaurentPolynomial.T_pow,
    map_mul, map_pow, map_neg, map_one]
  rw [show ((e 1 : ℤ) - e 2) = (e 1 : ℤ)*1 + (e 2 : ℤ)*(-1) by ring,
    LaurentPolynomial.T_add]
  simp only [mul_neg_one, mul_one]
  ring

theorem betaTriple_monomial_integral (e : Fin 3 →₀ ℕ) (c : ℂ) :
    integral (betaTriple (MvPolynomial.monomial e c)) =
      c * (if e 1 = e 2 then (-1 : ℂ)^e 1 *
        ((e 0).factorial * ((e 1).factorial : ℂ) / (e 0+e 1+1).factorial) else 0) := by
  rw [betaTriple_monomial]
  unfold integral
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  by_cases h : e 1 = e 2
  · simp only [h, sub_self, ite_true, eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X]
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, beta_factorial]
  · have hh : (e 1 : ℤ) - e 2 ≠ 0 := by omega
    simp [hh, h]

/-- A normalized-Haar transfer theorem for every polynomial in ad,b,c.
This includes every pure and marked power in Theorem 4.2. -/
theorem su2_polynomial_transfer (P : TriplePolynomial) :
    representativeIntegral SU2 (entryTriple P) = integral (betaTriple P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    change (∫ g : SU2, (entryTriple (MvPolynomial.monomial e c)).val g ∂normalizedHaar SU2) = _
    simp_rw [entryTriple_monomial]
    rw [integral_const_mul, balanced_entry_integral, betaTriple_monomial_integral]
  | add P Q hP hQ =>
    change representativeIntegral SU2 (entryTriple (P+Q)) = integralLinear (betaTriple (P+Q))
    rw [map_add, map_add, map_add, map_add, hP, hQ]
    rfl

end Hopf
end XZMathieuSU2Counterexamples
