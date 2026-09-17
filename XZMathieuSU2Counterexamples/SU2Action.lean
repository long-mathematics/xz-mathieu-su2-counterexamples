import XZMathieuSU2Counterexamples.SphereSymmetry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Instances.Matrix

/-! The defining SU(2) action, its sphere parametrization, and surface invariance. -/

noncomputable section
open Matrix MeasureTheory
namespace XZMathieuSU2Counterexamples.Hopf

/-- The actual determinant-one unitary matrix group. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

instance : MeasurableSpace SU2 := borel SU2
instance : BorelSpace SU2 := ⟨rfl⟩

/-- The standard special unitary matrix with prescribed first column. -/
def sphereMatrix (z : Sphere) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z.val.1, -star z.val.2; z.val.2, star z.val.1]

theorem sphereMatrix_mem (z : Sphere) : sphereMatrix z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hz : z.val.1 * star z.val.1 + z.val.2 * star z.val.2 = 1 := by
    simpa [a, Complex.normSq_eq_conj_mul_self, mul_comm] using congrArg Complex.ofReal z.property
  simp only [Complex.star_def] at hz
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sphereMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply] <;> first | (solve | ring) | linear_combination hz
  · simpa [sphereMatrix, Matrix.det_fin_two, mul_comm] using hz

def sphereToSU2 (z : Sphere) : SU2 := ⟨sphereMatrix z, sphereMatrix_mem z⟩

theorem su2_star_eq_adjugate (g : SU2) : star g.val = g.val.adjugate := by
  have hg := Matrix.mem_specialUnitaryGroup_iff.mp g.property
  apply left_inv_eq_right_inv hg.1.1
  rw [Matrix.mul_adjugate, hg.2, one_smul]

theorem su2_entries (g : SU2) :
    g.val 0 1 = -star (g.val 1 0) ∧ g.val 1 1 = star (g.val 0 0) := by
  have h := su2_star_eq_adjugate g
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
  simp [Matrix.adjugate_fin_two] at h01 h00
  constructor
  · apply star_injective
    simpa using h01
  · exact h00.symm

theorem su2_first_column (g : SU2) : a (g.val 0 0, g.val 1 0) = 1 := by
  have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1.1
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply] at h00
  apply Complex.ofReal_injective
  simpa [a, Complex.normSq_eq_conj_mul_self, mul_comm] using h00

def su2ToSphere (g : SU2) : Sphere := ⟨(g.val 0 0, g.val 1 0), su2_first_column g⟩

def su2SphereHomeomorph : SU2 ≃ₜ Sphere where
  toFun := su2ToSphere
  invFun := sphereToSU2
  left_inv g := by
    apply Subtype.ext
    ext i j
    have h := su2_entries g
    fin_cases i <;> fin_cases j <;> simp [sphereToSU2, sphereMatrix, su2ToSphere, h.1, h.2]
  right_inv z := by rfl
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    change Continuous (fun g : SU2 => (g.val 0 0, g.val 1 0))
    have h (i j : Fin 2) : Continuous (fun g : SU2 => g.val i j) :=
      continuous_subtype_val.matrix_elem i j
    exact (h 0 0).prodMk (h 1 0)
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    change Continuous sphereMatrix
    unfold sphereMatrix
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop

instance : CompactSpace SU2 := su2SphereHomeomorph.symm.compactSpace

instance : IsTopologicalGroup SU2 where
  continuous_mul := continuous_induced_rng.mpr
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  continuous_inv := continuous_induced_rng.mpr (continuous_subtype_val.star)

/-- The defining matrix action, expressed in the manuscript's pair coordinates. -/
def su2Linear (g : SU2) : Space ≃ₗ[ℂ] Space :=
  (LinearEquiv.finTwoArrow ℂ ℂ).symm.trans
    ((Matrix.UnitaryGroup.toLinearEquiv
      ⟨g.val, (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1⟩).trans
      (LinearEquiv.finTwoArrow ℂ ℂ))

theorem su2Linear_apply (g : SU2) (z : Space) :
    su2Linear g z = (g.val 0 0 * z.1 + g.val 0 1 * z.2,
      g.val 1 0 * z.1 + g.val 1 1 * z.2) := by
  change ((g.val *ᵥ ![z.1, z.2]) 0, (g.val *ᵥ ![z.1, z.2]) 1) = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem su2Linear_a (g : SU2) (z : Space) : a (su2Linear g z) = a z := by
  have h := su2_first_column g
  rw [su2Linear_apply, (su2_entries g).1, (su2_entries g).2]
  have heq : a (g.val 0 0 * z.1 + -star (g.val 1 0) * z.2,
      g.val 1 0 * z.1 + star (g.val 0 0) * z.2) =
      a (g.val 0 0, g.val 1 0) * a z := by
    simp [a, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [heq, h, one_mul]

theorem su2Linear_one (z : Space) : su2Linear 1 z = z := by
  rw [su2Linear_apply]
  simp

theorem su2Linear_mul (g h : SU2) (z : Space) :
    su2Linear (g * h) z = su2Linear g (su2Linear h z) := by
  simp only [su2Linear_apply, Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> dsimp <;> ring

instance : MulAction SU2 Space where
  smul := fun g z => su2Linear g z
  one_smul := su2Linear_one
  mul_smul := su2Linear_mul

theorem su2_smul_apply (g : SU2) (z : Space) :
    g • z = (g.val 0 0 * z.1 + g.val 0 1 * z.2,
      g.val 1 0 * z.1 + g.val 1 1 * z.2) := su2Linear_apply g z

instance : ContinuousSMul SU2 Space where
  continuous_smul := by
    simp only [su2_smul_apply]
    have h (i j : Fin 2) : Continuous (fun g : SU2 × Space => g.1.val i j) :=
      (continuous_subtype_val.comp continuous_fst).matrix_elem i j
    exact ((h 0 0).mul continuous_snd.fst |>.add ((h 0 1).mul continuous_snd.snd)).prodMk
      ((h 1 0).mul continuous_snd.fst |>.add ((h 1 1).mul continuous_snd.snd))

/-- The defining action is orthogonal for the real Euclidean norm. -/
def su2Isometry (g : SU2) : EuclideanPair ≃ₗᵢ[ℝ] EuclideanPair where
  toLinearEquiv := ((WithLp.linearEquiv 2 ℂ Space).trans
    ((su2Linear g).trans (WithLp.linearEquiv 2 ℂ Space).symm)).restrictScalars ℝ
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [norm_sq_eq_a]
    exact su2Linear_a g (WithLp.ofLp z)

instance : MulAction SU2 Sphere where
  smul g z := ⟨g • z.val, (su2Linear_a g z.val).trans z.property⟩
  one_smul z := Subtype.ext (one_smul SU2 z.val)
  mul_smul g h z := Subtype.ext (mul_smul g h z.val)

theorem su2_smul_val (g : SU2) (z : Sphere) : (g • z).val = g • z.val := rfl

instance : ContinuousSMul SU2 Sphere where
  continuous_smul := continuous_induced_rng.mpr
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))

theorem su2_sphereAction (g : SU2) (z : Sphere) : sphereAction (su2Isometry g) z = g • z := rfl

theorem su2_surfaceMeasure_preserving (g : SU2) :
    MeasurePreserving (fun z : Sphere => g • z) surfaceMeasure surfaceMeasure :=
  surfaceMeasure_preserving (su2Isometry g)

instance : SMulInvariantMeasure SU2 Sphere surfaceMeasure where
  measure_preimage_smul g _S hS := (su2_surfaceMeasure_preserving g).measure_preimage hS.nullMeasurableSet

/-- The explicit matrix carries the first basis vector to any prescribed unit vector. -/
theorem sphereToSU2_smul (z : Sphere) : sphereToSU2 z • ((1, 0) : Space) = z.val := by
  simp [su2_smul_apply, sphereToSU2, sphereMatrix]

theorem SU2_transitive_sphere (z w : Sphere) : ∃ g : SU2, g • z = w := by
  refine ⟨sphereToSU2 w * (sphereToSU2 z)⁻¹, ?_⟩
  apply Subtype.ext
  rw [su2_smul_val]
  have hz : (sphereToSU2 z)⁻¹ • z.val = ((1, 0) : Space) := by
    rw [← sphereToSU2_smul z, inv_smul_smul]
  rw [mul_smul, hz, sphereToSU2_smul]

end XZMathieuSU2Counterexamples.Hopf

/- Adapted from MathieuProperty/SU2Action.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
