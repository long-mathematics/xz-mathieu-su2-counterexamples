import XZMathieuSU2Counterexamples.SphereMeasure

/-! Orthogonal invariance of the actual Euclidean surface measure. -/

noncomputable section
open MeasureTheory Metric
open scoped Pointwise
namespace XZMathieuSU2Counterexamples.Hopf

def euclideanSphereAction (e : EuclideanPair ≃ₗᵢ[ℝ] EuclideanPair) :
    Metric.sphere (0 : EuclideanPair) 1 ≃ₜ Metric.sphere (0 : EuclideanPair) 1 where
  toFun z := ⟨e z.val, by
    rw [mem_sphere_zero_iff_norm, e.norm_map]
    exact mem_sphere_zero_iff_norm.mp z.property⟩
  invFun z := ⟨e.symm z.val, by
    rw [mem_sphere_zero_iff_norm, e.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp z.property⟩
  left_inv z := by ext; exact e.symm_apply_apply z.val
  right_inv z := by ext; exact e.apply_symm_apply z.val
  continuous_toFun := continuous_induced_rng.mpr (e.continuous.comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.mpr (e.symm.continuous.comp continuous_subtype_val)

theorem surface_cone_preimage (e : EuclideanPair ≃ₗᵢ[ℝ] EuclideanPair)
    (S : Set (Metric.sphere (0 : EuclideanPair) 1)) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (euclideanSphereAction e ⁻¹' S)) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' S)) := by
  ext y
  constructor
  · rintro ⟨r, hr, w, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨r, hr, e z.val, ⟨euclideanSphereAction e z, hz, rfl⟩, (e.map_smul r z.val).symm⟩
  · rintro ⟨r, hr, w, ⟨z, hz, rfl⟩, heq⟩
    refine ⟨r, hr, e.symm z.val, ⟨euclideanSphereAction e.symm z, ?_, rfl⟩, ?_⟩
    · have hz' : euclideanSphereAction e (euclideanSphereAction e.symm z) = z := by
        ext; exact e.apply_symm_apply z.val
      simpa only [Set.mem_preimage, hz'] using hz
    · apply e.injective
      simpa using heq

theorem euclideanSurface_preserving (e : EuclideanPair ≃ₗᵢ[ℝ] EuclideanPair) :
    MeasurePreserving (euclideanSphereAction e) euclideanSurface euclideanSurface := by
  refine ⟨(euclideanSphereAction e).measurable, ?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (euclideanSphereAction e).measurable hS]
  rw [euclideanSurface, Measure.toSphere_apply' _ ((euclideanSphereAction e).measurable hS),
    Measure.toSphere_apply' _ hS, surface_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

def sphereAction (e : EuclideanPair ≃ₗᵢ[ℝ] EuclideanPair) : Sphere ≃ₜ Sphere :=
  sphereHomeomorph.symm.trans ((euclideanSphereAction e).trans sphereHomeomorph)

theorem surfaceMeasure_preserving (e : EuclideanPair ≃ₗᵢ[ℝ] EuclideanPair) :
    MeasurePreserving (sphereAction e) surfaceMeasure surfaceMeasure := by
  refine ⟨(sphereAction e).measurable, ?_⟩
  unfold surfaceMeasure
  rw [Measure.map_map (sphereAction e).measurable sphereHomeomorph.measurable]
  have hcomp : sphereAction e ∘ sphereHomeomorph = sphereHomeomorph ∘ euclideanSphereAction e := by
    funext z
    simp [sphereAction]
  rw [hcomp, ← Measure.map_map sphereHomeomorph.measurable (euclideanSphereAction e).measurable,
    Measure.map_smul, (euclideanSurface_preserving e).map_eq]
  exact (euclideanSphereAction e).measurable.aemeasurable

end XZMathieuSU2Counterexamples.Hopf

/- Adapted from MathieuProperty/SphereSymmetry.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
