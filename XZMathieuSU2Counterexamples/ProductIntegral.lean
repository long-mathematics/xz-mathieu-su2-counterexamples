import XZMathieuSU2Counterexamples.Padding

noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples

def torusMeasure (k : ℕ) : Measure (Fin k → Circle) := Measure.pi (fun _ => normalizedHaar Circle)
instance (k : ℕ) : IsProbabilityMeasure (torusMeasure k) := by unfold torusMeasure; infer_instance
instance (k : ℕ) : (torusMeasure k).IsHaarMeasure := by unfold torusMeasure; infer_instance

theorem torusMeasure_eq_normalizedHaar (k : ℕ) : torusMeasure k = normalizedHaar (Fin k → Circle) := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace (torusMeasure k) (normalizedHaar (Fin k → Circle))
  have hc : Measure.haarScalarFactor (torusMeasure k) (normalizedHaar (Fin k → Circle)) = 1 := by
    apply ENNReal.coe_injective
    have hu := congrArg (fun μ : Measure (Fin k → Circle) => μ Set.univ) h
    simpa using hu.symm
  simpa [hc] using h

def torusMonomialHom {k : ℕ} (z : Fin k → Circle) : Multiplicative (Fin k → ℤ) →* ℂ where
  toFun e := ∏ j, (z j : ℂ)^(e.toAdd j)
  map_one' := by simp
  map_mul' e f := by
    change (∏ j, (z j : ℂ)^(e.toAdd j+f.toAdd j)) = _
    simp [zpow_add₀ (Circle.coe_ne_zero _), Finset.prod_mul_distrib]

def multiEval {k l : ℕ} (x : Fin l → ℝ) (z : Fin k → Circle) : MultiLaurent k l →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom (MvPolynomial.eval (fun i => (x i : ℂ)))
    (torusMonomialHom z) (fun _ _ => Commute.all _ _)

theorem multiEval_single {k l : ℕ} (x : Fin l → ℝ) (z : Fin k → Circle)
    (e : Fin k → ℤ) (p : MvPolynomial (Fin l) ℂ) :
    multiEval x z (AddMonoidAlgebra.single e p) =
      MvPolynomial.eval (fun i => (x i : ℂ)) p * ∏ j, (z j : ℂ)^(e j) := by
  rw [multiEval, AddMonoidAlgebra.liftNCRingHom_single]
  rfl

theorem multiEval_continuous {k l : ℕ} (x : Fin l → ℝ) (f : MultiLaurent k l) :
    Continuous (fun z : Fin k → Circle => multiEval x z f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : Fin k → Circle => (0 : ℂ)))
  | add f g hf hg =>
    have he : (fun z => multiEval x z (f+g)) = (fun z => multiEval x z f) + (fun z => multiEval x z g) := by
      funext z; exact map_add _ _ _
    rw [he]; exact hf.add hg
  | single e p =>
    simp_rw [multiEval_single]
    apply continuous_const.mul
    apply continuous_finsetProd
    intro j _
    exact (continuous_subtype_val.comp (continuous_apply j)).zpow₀ (e j)
      (fun z => Or.inl (Circle.coe_ne_zero (z j)))

theorem multiCircle_constantTerm {k l : ℕ} (x : Fin l → ℝ) (f : MultiLaurent k l) :
    (∫ z, multiEval x z f ∂torusMeasure k) = MvPolynomial.eval (fun i => (x i : ℂ)) (f.coeff 0) := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [integral_add ((multiEval_continuous x f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) ((multiEval_continuous x g).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)), hf, hg]
  | single e p =>
    simp_rw [multiEval_single]
    rw [integral_const_mul]
    unfold torusMeasure
    rw [integral_fintype_prod_eq_prod (fun j (z : Circle) => (z : ℂ)^(e j))
      (μ := fun _ : Fin k => normalizedHaar Circle)]
    simp_rw [circle_zpow_integral]
    by_cases he : e = 0
    · subst e; simp
    · obtain ⟨j,hj⟩ := Function.ne_iff.mp he
      have hp : (∏ i : Fin k, if e i = 0 then (1 : ℂ) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simpa using hj)
      rw [hp]
      simp [AddMonoidAlgebra.coeff_single, he]

/-- The multidimensional functional is literally cube integration followed by
normalized Haar integration on the entire finite torus. -/
theorem multiIntegral_eq_product {k l : ℕ} (f : MultiLaurent k l) :
    multiIntegral f = ∫ x, ∫ z, multiEval x z f ∂normalizedHaar (Fin k → Circle) ∂cubeMeasure l := by
  rw [← torusMeasure_eq_normalizedHaar]
  simp only [multiCircle_constantTerm, multiIntegral]

/-- Padding is the usual inclusion using exactly one interval and torus coordinate. -/
theorem pad_eval {k l : ℕ} (j : Fin k) (i : Fin l) (f : Laurent)
    (x : Fin l → ℝ) (z : Fin k → Circle) :
    multiEval x z (pad j i f) = circleEval (z j) (specialize (x i : ℂ) f) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp [hf,hg]
  | C_mul_T n p =>
    rw [pad_monomial, multiEval_single, padCoefficient_eval]
    simp [padExponent, Pi.single_apply, Finset.prod_ite_eq', circleEval_monomial]

end XZMathieuSU2Counterexamples
