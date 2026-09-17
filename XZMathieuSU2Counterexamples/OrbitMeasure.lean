import XZMathieuSU2Counterexamples.OrbitAverage
import Mathlib.MeasureTheory.Group.LIntegral

/-! Haar orbits of transitive compact group actions realize the invariant probability measure. -/

noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]

theorem measurePreserving_transitive_orbit (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (z : X) :
    MeasurePreserving (fun g : G => g • z) (normalizedHaar G) μ := by
  have hc : Measurable (fun g : G => g • z) := (continuous_id.smul continuous_const).measurable
  refine ⟨hc, Measure.ext_of_lintegral _ ?_⟩
  intro f hf
  rw [lintegral_map hf hc]
  have hconstant (x : X) :
      (∫⁻ g : G, f (g • x) ∂normalizedHaar G) = ∫⁻ g : G, f (g • z) ∂normalizedHaar G := by
    obtain ⟨h, rfl⟩ := htrans z x
    simpa only [mul_smul] using
      lintegral_mul_right_eq_self (μ := normalizedHaar G) (fun g : G => f (g • z)) h
  calc
    (∫⁻ g : G, f (g • z) ∂normalizedHaar G) =
        ∫⁻ x : X, ∫⁻ g : G, f (g • x) ∂normalizedHaar G ∂μ := by simp [hconstant]
    _ = ∫⁻ g : G, ∫⁻ x : X, f (g • x) ∂μ ∂normalizedHaar G := by
      apply lintegral_lintegral_swap
      exact (hf.comp (continuous_snd.smul continuous_fst).measurable).aemeasurable
    _ = ∫⁻ x : X, f x ∂μ := by
      simp_rw [(measurePreserving_smul _ μ).lintegral_comp hf]
      simp

end XZMathieuSU2Counterexamples

/- Adapted from MathieuProperty/OrbitMeasure.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
