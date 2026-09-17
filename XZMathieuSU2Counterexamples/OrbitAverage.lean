import XZMathieuSU2Counterexamples.Haar
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-! Orbit averaging for finite invariant measures. Product integrability follows
from invariance for integrable functions, and from compact support for continuous ones. -/

noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]

theorem integrable_orbit_function (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) {f : X → ℂ} (hf : Continuous f) :
    Integrable (fun p : G × X => f (p.1 • p.2)) ((normalizedHaar G).prod μ) := by
  have hc : Continuous (fun p : G × X => f (p.1 • p.2)) := hf.comp continuous_smul
  have hi := ContinuousOn.integrableOn_compact (μ := (normalizedHaar G).prod μ)
    (isCompact_univ.prod hμ) hc.continuousOn
  have hmem : ∀ᵐ p : G × X ∂(normalizedHaar G).prod μ, p ∈ Set.univ ×ˢ μ.support := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := normalizedHaar G) (ν := μ)).ae
      μ.support_mem_ae] with p hp
    exact ⟨Set.mem_univ _, hp⟩
  change Integrable _ (((normalizedHaar G).prod μ).restrict (Set.univ ×ˢ μ.support)) at hi
  rw [Measure.restrict_eq_self_of_ae_mem hmem] at hi
  exact hi

omit [T2Space G] [T2Space X] in
/-- Averaging a measure-preserving action against a probability Haar measure
preserves the measure, including for merely measurable test functions. -/
theorem measurePreserving_smul_prod (μ : Measure X) [IsFiniteMeasure μ]
    [SMulInvariantMeasure G X μ] :
    MeasurePreserving (fun p : G × X => p.1 • p.2) ((normalizedHaar G).prod μ) μ := by
  have hc : Measurable (fun p : G × X => p.1 • p.2) := continuous_smul.measurable
  refine ⟨hc, ?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hc hS, Measure.prod_apply (hc hS)]
  have hsections (g : G) : μ (Prod.mk g ⁻¹' ((fun p : G × X => p.1 • p.2) ⁻¹' S)) = μ S :=
    SMulInvariantMeasure.measure_preimage_smul g hS
  simp_rw [hsections]
  simp

omit [T2Space G] [T2Space X] in
/-- The manuscript's orbit averaging identity for every μ-integrable complex
function. Product integrability follows from invariance, rather than being assumed. -/
theorem orbit_average_integrable (μ : Measure X) [IsFiniteMeasure μ]
    [SMulInvariantMeasure G X μ] {f : X → ℂ} (hf : Integrable f μ) :
    (∫ x, (∫ g, f (g • x) ∂normalizedHaar G) ∂μ) = ∫ x, f x ∂μ := by
  have hi := (measurePreserving_smul_prod (G := G) μ).integrable_comp_of_integrable hf
  rw [← integral_integral_swap (f := fun (g : G) (x : X) => f (g • x)) hi]
  simp only [integral_smul_eq_self]
  simp

/-- Orbit averaging with no unproved Fubini or integrability assumption. -/
theorem orbit_average (μ : Measure X) [IsFiniteMeasure μ] [SMulInvariantMeasure G X μ]
    (hμ : IsCompact μ.support) {f : X → ℂ} (hf : Continuous f) :
    (∫ x, (∫ g, f (g • x) ∂normalizedHaar G) ∂μ) = ∫ x, f x ∂μ := by
  rw [← integral_integral_swap (integrable_orbit_function (G := G) μ hμ hf)]
  simp only [integral_smul_eq_self]
  simp

end XZMathieuSU2Counterexamples

/- Adapted from MathieuProperty/OrbitAverage.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
