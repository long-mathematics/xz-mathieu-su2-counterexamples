import XZMathieuSU2Counterexamples.LaurentIntegral
import XZMathieuSU2Counterexamples.Haar
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples

instance : MeasurableSpace Circle := borel Circle
instance : BorelSpace Circle := ⟨rfl⟩

theorem circle_zpow_integral (k : ℤ) :
    (∫ z : Circle, (z : ℂ)^k ∂normalizedHaar Circle) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  rw [ite_eq_right hk]
  have hz : ((Circle.exp (Real.pi / k) : Circle) : ℂ)^k = -1 := by
    rw [Circle.coe_exp, ← Complex.exp_int_mul]
    have hc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have he : (k : ℂ) * (((Real.pi / k : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [he, Complex.exp_pi_mul_I]
  have h := integral_mul_left_eq_self (μ := normalizedHaar Circle)
    (fun z : Circle => (z : ℂ)^k) (Circle.exp (Real.pi / k))
  simp only [Circle.coe_mul, mul_zpow, hz, integral_const_mul] at h
  linear_combination -h / 2

def circleEval (z : Circle) : ScalarLaurent →+* ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) (Circle.toUnits z)

theorem circleEval_monomial (z : Circle) (k : ℤ) (c : ℂ) :
    circleEval z (LaurentPolynomial.C c * LaurentPolynomial.T k) = c * (z : ℂ)^k := by
  simp [circleEval]

@[fun_prop] theorem circleEval_continuous (f : ScalarLaurent) :
    Continuous (fun z : Circle => circleEval z f) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    have he : (fun z : Circle => circleEval z (f+g)) =
        (fun z => circleEval z f) + (fun z => circleEval z g) := by
      funext z
      exact map_add (circleEval z) f g
    rw [he]
    exact hf.add hg
  | C_mul_T k c =>
    simp_rw [circleEval_monomial]
    exact continuous_const.mul (continuous_subtype_val.zpow₀ k (fun z => Or.inl (Circle.coe_ne_zero z)))

theorem circle_constantTerm (f : ScalarLaurent) :
    (∫ z : Circle, circleEval z f ∂normalizedHaar Circle) = f.coeff 0 := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [integral_add ((circleEval_continuous f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) ((circleEval_continuous g).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)), hf, hg]
  | C_mul_T k c =>
    simp_rw [circleEval_monomial]
    rw [integral_const_mul, circle_zpow_integral]
    simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    split_ifs <;> simp_all

/-- Equation I-def with genuine normalized circle Haar measure. -/
theorem integral_eq_interval_circle (f : Laurent) : integral f =
    ∫ x in (0 : ℝ)..1, ∫ z : Circle, circleEval z (specialize (x : ℂ) f) ∂normalizedHaar Circle := by
  simp only [circle_constantTerm, specialize_coeff, integral]

end XZMathieuSU2Counterexamples
