import XZMathieuSU2Counterexamples.CircleIntegral
import XZMathieuSU2Counterexamples.XZWitness
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory Polynomial
namespace XZMathieuSU2Counterexamples

abbrev MultiLaurent (k l : ℕ) := AddMonoidAlgebra (MvPolynomial (Fin l) ℂ) (Fin k → ℤ)

def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)
instance : IsProbabilityMeasure unitIntervalMeasure where
  measure_univ := by simp [unitIntervalMeasure]

def cubeMeasure (l : ℕ) : Measure (Fin l → ℝ) := Measure.pi (fun _ => unitIntervalMeasure)

theorem cube_polynomial_integrable {l : ℕ} (p : MvPolynomial (Fin l) ℂ) :
    Integrable (fun x : Fin l → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) p) (cubeMeasure l) := by
  have hc : Continuous (fun x : Fin l → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) p) :=
    p.continuous_eval.comp (by fun_prop)
  have hi := hc.continuousOn.integrableOn_compact (μ := Measure.pi (fun _ : Fin l => (volume : Measure ℝ)))
    (isCompact_univ_pi (fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)))
  simpa only [IntegrableOn, Measure.restrict_pi_pi, cubeMeasure, unitIntervalMeasure] using hi

def multiIntegral {k l : ℕ} (f : MultiLaurent k l) : ℂ :=
  ∫ x, MvPolynomial.eval (fun i => (x i : ℂ)) (f.coeff 0) ∂cubeMeasure l

def multiIntegralLinear (k l : ℕ) : MultiLaurent k l →ₗ[ℂ] ℂ where
  toFun := multiIntegral
  map_add' f g := by
    simp only [multiIntegral, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
    exact integral_add (cube_polynomial_integrable _) (cube_polynomial_integrable _)
  map_smul' c f := by simp [multiIntegral, integral_const_mul]

def padExponent {k : ℕ} (j : Fin k) : ℤ →+ (Fin k → ℤ) where
  toFun n := Pi.single j n
  map_zero' := by simp
  map_add' n m := by ext i; by_cases h : i=j <;> simp [h]

theorem padExponent_injective {k : ℕ} (j : Fin k) : Function.Injective (padExponent j) := by
  intro a b h
  have hh := congrFun h j
  simpa [padExponent] using hh

def padCoefficient {l : ℕ} (i : Fin l) : ℂ[X] →+* MvPolynomial (Fin l) ℂ :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i)

def pad {k l : ℕ} (j : Fin k) (i : Fin l) : Laurent →+* MultiLaurent k l :=
  (AddMonoidAlgebra.mapDomainRingHom _ (padExponent j)).comp
    (AddMonoidAlgebra.mapRingHom ℤ (padCoefficient i))

theorem pad_monomial {k l : ℕ} (j : Fin k) (i : Fin l) (n : ℤ) (p : ℂ[X]) :
    pad j i (LaurentPolynomial.C p * LaurentPolynomial.T n) =
      AddMonoidAlgebra.single (padExponent j n) (padCoefficient i p) := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  simp only [pad, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single,
    AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]

theorem pad_coeff {k l : ℕ} (j : Fin k) (i : Fin l) (f : Laurent) (n : ℤ) :
    (pad j i f).coeff (padExponent j n) = padCoefficient i (f.coeff n) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | C_mul_T m p =>
    rw [pad_monomial]
    simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp only [(padExponent_injective j).eq_iff]
    split_ifs <;> simp

theorem padCoefficient_eval {l : ℕ} (i : Fin l) (p : ℂ[X]) (x : Fin l → ℝ) :
    MvPolynomial.eval (fun j => (x j : ℂ)) (padCoefficient i p) = p.eval (x i : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n c => simp [padCoefficient, Polynomial.eval₂_monomial]

/-- Finite product integration really eliminates the unused interval coordinates. -/
theorem pad_integral {k l : ℕ} (j : Fin k) (i : Fin l) (f : Laurent) :
    multiIntegral (pad j i f) = integral f := by
  have hc := pad_coeff j i f 0
  simp only [map_zero] at hc
  simp only [multiIntegral, hc, padCoefficient_eval, cubeMeasure]
  rw [integral_comp_eval (μ := fun _ : Fin l => unitIntervalMeasure) (i := i)
    (f := fun t : ℝ => (f.coeff 0).eval (t : ℂ))
    ((f.coeff 0).continuous.comp Complex.continuous_ofReal).aestronglyMeasurable]
  simp only [unitIntervalMeasure, integral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

def MixedXZConjecture (k l : ℕ) : Prop := ∀ f : MultiLaurent k l,
  (∀ n : ℕ, 1 ≤ n → multiIntegral (f^n) = 0) →
  (0 : Fin k → ℝ) ∉ convexHull ℝ ((fun e : Fin k → ℤ => fun j => (e j : ℝ)) ''
    (f.coeff.support : Set (Fin k → ℤ)))

theorem padded_zero_support {k l : ℕ} (j : Fin k) (i : Fin l) :
    (0 : Fin k → ℤ) ∈ (pad j i basic).coeff.support := by
  rw [Finsupp.mem_support_iff]
  have hc := pad_coeff j i basic 0
  simp only [map_zero] at hc
  rw [hc]
  intro h
  have he := congrArg (MvPolynomial.eval (0 : Fin l → ℂ)) h
  simp [basic_coeff, padCoefficient] at he

/-- Corollary 2.2 for every genuinely mixed finite pair of dimensions. -/
theorem all_mixed_xz (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ¬ MixedXZConjecture k l ∧ ¬ IsMathieuSubspace (LinearMap.ker (multiIntegralLinear k l)) := by
  let j : Fin k := ⟨0,by omega⟩
  let i : Fin l := ⟨0,by omega⟩
  have hp (n : ℕ) (hn : 1 ≤ n) : multiIntegral (pad j i basic ^ n) = 0 := by
    rw [← map_pow, pad_integral]
    exact basic_pure n hn
  have hm (n : ℕ) (hn : 1 ≤ n) :
      multiIntegral (pad j i (LaurentPolynomial.T (-1)) * pad j i basic ^ n) ≠ 0 := by
    rw [← map_pow, ← map_mul, pad_integral]
    exact basic_marked_ne_zero n hn
  constructor
  · intro h
    apply h (pad j i basic) hp
    apply subset_convexHull ℝ
    exact ⟨0,padded_zero_support j i,by ext; simp⟩
  · exact not_isMathieuSubspace_of_witness _ (pad j i basic) (pad j i (LaurentPolynomial.T (-1))) hp hm

end XZMathieuSU2Counterexamples
