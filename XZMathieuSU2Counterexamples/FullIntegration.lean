import XZMathieuSU2Counterexamples.SU2Integration
import XZMathieuSU2Counterexamples.CircleIntegral
import Mathlib.Topology.Algebra.MvPolynomial

set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples

theorem continuous_circle_integral {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] {f : X → Circle → ℂ}
    (hf : Continuous f.uncurry) : Continuous (fun x => ∫ z, f x z ∂normalizedHaar Circle) := by
  simpa using continuous_parametric_integral_of_continuous (μ := normalizedHaar Circle)
    hf (s := Set.univ) isCompact_univ

namespace Hopf
abbrev CoordinatePolynomial := MvPolynomial (Fin 4) ℂ

def entryCoordinates : CoordinatePolynomial →ₐ[ℂ] representativeFunctions (G := SU2) :=
  MvPolynomial.aeval ![su2Entry 0 0, su2Entry 1 0, su2Entry 0 1, su2Entry 1 1]

def betaPoint (x : ℝ) (z₁ z₂ : Circle) : Fin 4 → ℂ :=
  ![(1-(x : ℂ))*(z₂ : ℂ), (x : ℂ)*(z₁ : ℂ), -(↑(z₁⁻¹) : ℂ), (↑(z₂⁻¹) : ℂ)]

def betaEval (P : CoordinatePolynomial) (x : ℝ) (z₁ z₂ : Circle) : ℂ :=
  MvPolynomial.eval (betaPoint x z₁ z₂) P

def betaAverage (P : CoordinatePolynomial) (x : ℝ) : ℂ :=
  ∫ z₁ : Circle, ∫ z₂ : Circle, betaEval P x z₁ z₂ ∂normalizedHaar Circle ∂normalizedHaar Circle

def betaIntegral (P : CoordinatePolynomial) : ℂ := ∫ x in (0 : ℝ)..1, betaAverage P x

theorem betaEval_continuous (P : CoordinatePolynomial) :
    Continuous (fun v : (ℝ × Circle) × Circle => betaEval P v.1.1 v.1.2 v.2) := by
  apply P.continuous_eval.comp
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [betaPoint] <;> fun_prop (disch := intro v; exact Circle.coe_ne_zero _)

theorem betaInner_continuous (P : CoordinatePolynomial) :
    Continuous (fun v : ℝ × Circle => ∫ z₂, betaEval P v.1 v.2 z₂ ∂normalizedHaar Circle) :=
  continuous_circle_integral (betaEval_continuous P)

theorem betaAverage_continuous (P : CoordinatePolynomial) : Continuous (betaAverage P) :=
  continuous_circle_integral (betaInner_continuous P)

theorem betaEval_add (P Q : CoordinatePolynomial) (x : ℝ) (z₁ z₂ : Circle) :
    betaEval (P+Q) x z₁ z₂ = betaEval P x z₁ z₂ + betaEval Q x z₁ z₂ := by
  simp [betaEval]

theorem betaAverage_add (P Q : CoordinatePolynomial) (x : ℝ) :
    betaAverage (P+Q) x = betaAverage P x + betaAverage Q x := by
  have hi (P : CoordinatePolynomial) (z₁ : Circle) :
      Integrable (betaEval P x z₁) (normalizedHaar Circle) :=
    ((betaEval_continuous P).comp (show Continuous (fun z₂ : Circle => ((x,z₁),z₂)) by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj (P : CoordinatePolynomial) :
      Integrable (fun z₁ => ∫ z₂, betaEval P x z₁ z₂ ∂normalizedHaar Circle) (normalizedHaar Circle) :=
    ((betaInner_continuous P).comp (show Continuous (fun z₁ : Circle => (x,z₁)) by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold betaAverage
  simp_rw [betaEval_add, integral_add (hi P _) (hi Q _)]
  exact integral_add (hj P) (hj Q)

theorem betaIntegral_add (P Q : CoordinatePolynomial) : betaIntegral (P+Q) = betaIntegral P + betaIntegral Q := by
  simp only [betaIntegral, betaAverage_add]
  exact intervalIntegral.integral_add ((betaAverage_continuous P).intervalIntegrable 0 1)
    ((betaAverage_continuous Q).intervalIntegrable 0 1)

theorem entryCoordinates_monomial (e : Fin 4 →₀ ℕ) (c : ℂ) (g : SU2) :
    (entryCoordinates (MvPolynomial.monomial e c)).val g =
      c * entryMonomial (e 0) (e 1) (e 2) (e 3) g := by
  simp only [entryCoordinates, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  change c * (g.val 0 0^e 0 * (g.val 1 0^e 1 * (g.val 0 1^e 2 * (g.val 1 1^e 3 * 1)))) = _
  simp only [entryMonomial]
  ring

theorem betaEval_monomial (e : Fin 4 →₀ ℕ) (c : ℂ) (x : ℝ) (z₁ z₂ : Circle) :
    betaEval (MvPolynomial.monomial e c) x z₁ z₂ =
      (c * (-1 : ℂ)^e 2 * (1-(x : ℂ))^e 0 * (x : ℂ)^e 1) *
        (z₁ : ℂ)^((e 1 : ℤ)-e 2) * (z₂ : ℂ)^((e 0 : ℤ)-e 3) := by
  simp only [betaEval, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  change c * (((1-(x : ℂ))*(z₂ : ℂ))^e 0 * (((x : ℂ)*(z₁ : ℂ))^e 1 *
    ((-((z₁ : ℂ)⁻¹))^e 2 * (((z₂ : ℂ)⁻¹)^e 3 * 1)))) = _
  rw [neg_pow ((z₁ : ℂ)⁻¹) (e 2)]
  simp only [zpow_sub₀ (Circle.coe_ne_zero _), zpow_natCast, div_eq_mul_inv, inv_pow, mul_pow]
  ring

theorem betaAverage_monomial (e : Fin 4 →₀ ℕ) (c : ℂ) (x : ℝ) :
    betaAverage (MvPolynomial.monomial e c) x =
      if e 0 = e 3 ∧ e 1 = e 2 then c * (-1 : ℂ)^e 1 * (1-(x : ℂ))^e 0 * (x : ℂ)^e 1 else 0 := by
  unfold betaAverage
  simp_rw [betaEval_monomial, integral_const_mul, integral_mul_const, circle_zpow_integral]
  by_cases h0 : e 0 = e 3 <;> by_cases h1 : e 1 = e 2
  all_goals simp [h0, h1, sub_eq_zero, integral_const_mul, circle_zpow_integral]

theorem betaIntegral_monomial (e : Fin 4 →₀ ℕ) (c : ℂ) :
    betaIntegral (MvPolynomial.monomial e c) = c *
      (if e 0 = e 3 ∧ e 1 = e 2 then
        (-1 : ℂ)^e 1 * ((e 0).factorial * ((e 1).factorial : ℂ) / (e 0+e 1+1).factorial) else 0) := by
  simp only [betaIntegral, betaAverage_monomial]
  by_cases h : e 0 = e 3 ∧ e 1 = e 2
  · simp only [h, and_self, ite_true]
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, beta_factorial]
  · simp [h]

/-- Lemma 4.1 for every polynomial in all four matrix entries. -/
theorem su2_integration (P : CoordinatePolynomial) :
    representativeIntegral SU2 (entryCoordinates P) = betaIntegral P := by
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    change (∫ g : SU2, (entryCoordinates (MvPolynomial.monomial e c)).val g ∂normalizedHaar SU2) = _
    simp_rw [entryCoordinates_monomial]
    rw [integral_const_mul, su2_monomial, betaIntegral_monomial]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, betaIntegral_add]

theorem entryCoordinates_apply (P : CoordinatePolynomial) (g : SU2) :
    (entryCoordinates P).val g =
      MvPolynomial.eval ![g.val 0 0, g.val 1 0, g.val 0 1, g.val 1 1] P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [entryCoordinates]
  | add P Q hP hQ =>
    simp only [map_add]
    change (entryCoordinates P).val g + (entryCoordinates Q).val g = _
    rw [hP,hQ]
  | mul_X P i hP =>
    simp only [map_mul, entryCoordinates, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    change (entryCoordinates P).val g *
      (![su2Entry 0 0, su2Entry 1 0, su2Entry 0 1, su2Entry 1 1] i).val g = _
    rw [hP]
    fin_cases i <;> rfl

/-- Literal manuscript-facing version of Lemma 4.1. -/
theorem su2_integration_formula (P : CoordinatePolynomial) :
    (∫ g : SU2, MvPolynomial.eval ![g.val 0 0, g.val 1 0, g.val 0 1, g.val 1 1] P
      ∂normalizedHaar SU2) =
    ∫ x in (0 : ℝ)..1, ∫ z₁ : Circle, ∫ z₂ : Circle,
      MvPolynomial.eval ![(1-(x : ℂ))*(z₂ : ℂ), (x : ℂ)*(z₁ : ℂ),
        -(z₁ : ℂ)⁻¹, (z₂ : ℂ)⁻¹] P ∂normalizedHaar Circle ∂normalizedHaar Circle := by
  have h := su2_integration P
  change (∫ g : SU2, (entryCoordinates P).val g ∂normalizedHaar SU2) = _ at h
  simpa only [entryCoordinates_apply, betaIntegral, betaAverage, betaEval, betaPoint, Circle.coe_inv] using h

end Hopf
end XZMathieuSU2Counterexamples
