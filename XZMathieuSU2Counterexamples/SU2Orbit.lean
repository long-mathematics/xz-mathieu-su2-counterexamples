import XZMathieuSU2Counterexamples.SU2Action
import XZMathieuSU2Counterexamples.OrbitMeasure

/-! Identification of SU(2) Haar orbits with normalized Euclidean sphere measure. -/

noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples.Hopf

/-- Haar orbits give the manuscript's actual surface measure, at every base point. -/
theorem su2_orbit_measurePreserving (z : Sphere) :
    MeasurePreserving (fun g : SU2 => g • z) (normalizedHaar SU2) surfaceMeasure :=
  measurePreserving_transitive_orbit surfaceMeasure SU2_transitive_sphere z

theorem su2_orbit_map (z : Sphere) :
    Measure.map (fun g : SU2 => g • z) (normalizedHaar SU2) = surfaceMeasure :=
  (su2_orbit_measurePreserving z).map_eq

theorem su2_orbit_integral (z : Sphere) {f : Sphere → ℂ} (hf : Continuous f) :
    (∫ g : SU2, f (g • z) ∂normalizedHaar SU2) = ∫ w, f w ∂surfaceMeasure := by
  rw [← su2_orbit_map z]
  exact (integral_map_of_stronglyMeasurable
    (su2_orbit_measurePreserving z).measurable hf.stronglyMeasurable).symm

/-- Every vector has a nonnegative radius and a unit direction; zero is included. -/
theorem exists_radial_direction (z : Space) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ w : Sphere, z = (r : ℂ) • w.val ∧ r ^ 2 = a z := by
  by_cases hz : z = 0
  · subst z
    refine ⟨0, le_rfl, ⟨(1, 0), by simp [a]⟩, ?_, ?_⟩ <;> simp [a]
  · let r := Real.sqrt (a z)
    have ha : 0 < a z := lt_of_le_of_ne (a_nonneg z) (Ne.symm ((a_eq_zero_iff z).not.mpr hz))
    have hr : 0 < r := Real.sqrt_pos.mpr ha
    have hr2 : r ^ 2 = a z := Real.sq_sqrt ha.le
    have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hw : a ((r : ℂ)⁻¹ • z) = 1 := by
      rw [a_smul, map_inv₀, Complex.normSq_ofReal]
      rw [← pow_two, ← hr2]
      exact inv_mul_cancel₀ (pow_ne_zero _ hr.ne')
    refine ⟨r, hr.le, ⟨(r : ℂ)⁻¹ • z, hw⟩, ?_, hr2⟩
    simp [smul_smul, hc]

theorem su2_smul_complex (g : SU2) (c : ℂ) (z : Space) :
    g • (c • z) = c • (g • z) := (su2Linear g).map_smul c z

/-- Transitivity on every Euclidean sphere, stated in the manuscript's coordinates. -/
theorem SU2_transitive_equal_a (z w : Space) (h : a z = a w) : ∃ g : SU2, g • z = w := by
  obtain ⟨r, hr, z', hz, hr2⟩ := exists_radial_direction z
  obtain ⟨s, hs, w', hw, hs2⟩ := exists_radial_direction w
  have hrs : r = s := (sq_eq_sq₀ hr hs).mp (hr2.trans (h.trans hs2.symm))
  obtain ⟨g, hg⟩ := SU2_transitive_sphere z' w'
  refine ⟨g, ?_⟩
  rw [hz, hw, hrs, su2_smul_complex]
  exact congrArg (fun x : Sphere => (s : ℂ) • x.val) hg


end XZMathieuSU2Counterexamples.Hopf

/- Adapted from MathieuProperty/SU2Orbit.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
