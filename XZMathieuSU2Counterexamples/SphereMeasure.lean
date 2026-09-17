import XZMathieuSU2Counterexamples.HopfAlgebra
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Measure.Support

/-! The Euclidean sphere model, normalized surface measure, and integrability
used for the SU(2) moment recurrence. -/

noncomputable section
open MeasureTheory Metric
open scoped Pointwise
namespace XZMathieuSU2Counterexamples.Hopf

abbrev EuclideanPair := WithLp 2 Space

instance : TopologicalSpace Sphere := inferInstanceAs (TopologicalSpace {z : Space // a z = 1})
instance : MeasurableSpace Sphere := inferInstanceAs (MeasurableSpace {z : Space // a z = 1})
instance : BorelSpace Sphere := inferInstanceAs (BorelSpace {z : Space // a z = 1})
instance : SecondCountableTopology Sphere :=
  inferInstanceAs (SecondCountableTopology {z : Space // a z = 1})
instance : T2Space Sphere := inferInstanceAs (T2Space {z : Space // a z = 1})

theorem norm_sq_eq_a (z : EuclideanPair) : ‖z‖ ^ 2 = a (WithLp.ofLp z) := by
  simp [a, Complex.normSq_eq_norm_sq, WithLp.prod_norm_sq_eq_of_L2]

def sphereHomeomorph : Metric.sphere (0 : EuclideanPair) 1 ≃ₜ Sphere where
  toFun z := ⟨WithLp.ofLp z.val, by
    rw [← norm_sq_eq_a]
    have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
    simp [hz]⟩
  invFun z := ⟨WithLp.toLp 2 z.val, by
    change dist (WithLp.toLp 2 z.val) 0 = 1
    rw [dist_zero_right]
    have h : ‖WithLp.toLp 2 z.val‖ ^ 2 = 1 := by rw [norm_sq_eq_a]; exact z.property
    nlinarith [norm_nonneg (WithLp.toLp 2 z.val)]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.mpr
    ((WithLp.prod_continuous_ofLp 2 ℂ ℂ).comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.mpr
    ((WithLp.prod_continuous_toLp 2 ℂ ℂ).comp continuous_subtype_val)

instance : CompactSpace Sphere := sphereHomeomorph.compactSpace

@[fun_prop] theorem continuous_a : Continuous a := by unfold a; fun_prop
/-- Unnormalized Euclidean surface measure, from the cone construction. -/
def euclideanSurface : Measure (Metric.sphere (0 : EuclideanPair) 1) :=
  (volume : Measure EuclideanPair).toSphere

instance : IsFiniteMeasure euclideanSurface := by
  unfold euclideanSurface
  infer_instance

theorem euclideanSurface_ne_zero : euclideanSurface ≠ 0 :=
  Measure.toSphere_ne_zero _

/-- The manuscript's normalized Euclidean surface measure transported to `a(z)=1`. -/
def surfaceMeasure : Measure Sphere :=
  Measure.map sphereHomeomorph ((euclideanSurface Set.univ)⁻¹ • euclideanSurface)

instance : IsProbabilityMeasure ((euclideanSurface Set.univ)⁻¹ • euclideanSurface) where
  measure_univ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simpa using euclideanSurface_ne_zero) (measure_ne_top _ _)

instance : IsProbabilityMeasure surfaceMeasure := by
  unfold surfaceMeasure
  exact Measure.isProbabilityMeasure_map_iff sphereHomeomorph.measurable.aemeasurable |>.mpr inferInstance


end XZMathieuSU2Counterexamples.Hopf

/- Adapted from MathieuProperty/SphereMeasure.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
