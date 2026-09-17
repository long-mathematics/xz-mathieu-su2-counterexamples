import XZMathieuSU2Counterexamples.SphereMomentRecurrence
import XZMathieuSU2Counterexamples.Bernstein

set_option maxRecDepth 4000
noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples.Hopf

def definingMatrixRepresentation : MatrixRepresentation SU2 (Fin 2) where
  toMonoidHom := (Matrix.specialUnitaryGroup (Fin 2) ℂ).subtype
  continuous_entry i j := continuous_subtype_val.matrix_elem i j

def su2Entry (i j : Fin 2) : representativeFunctions (G := SU2) :=
  ⟨definingMatrixRepresentation.entry i j, entry_mem_representative _ i j⟩

@[simp] theorem su2Entry_apply (i j : Fin 2) (g : SU2) : (su2Entry i j).val g = g.val i j := rfl

def basePoint : Sphere := ⟨(1,0), by simp [a]⟩

theorem su2_smul_basePoint (g : SU2) : g • basePoint = su2ToSphere g := by
  apply Subtype.ext
  change g • ((1,0) : Space) = (g.val 0 0, g.val 1 0)
  simp [su2_smul_apply]

theorem su2_firstColumn_integral {f : Sphere → ℂ} (hf : Continuous f) :
    (∫ g : SU2, f (su2ToSphere g) ∂normalizedHaar SU2) = ∫ z, f z ∂surfaceMeasure := by
  simpa only [su2_smul_basePoint] using su2_orbit_integral basePoint hf

/-- Matrix layout in the paper is [a,c;b,d]. -/
def entryMonomial (r s t u : ℕ) (g : SU2) : ℂ :=
  g.val 0 0 ^ r * g.val 1 0 ^ s * g.val 0 1 ^ t * g.val 1 1 ^ u

@[fun_prop] theorem continuous_entryMonomial (r s t u : ℕ) :
    Continuous (entryMonomial r s t u) :=
  (((continuous_subtype_val.matrix_elem 0 0).pow r).mul
    ((continuous_subtype_val.matrix_elem 1 0).pow s)).mul
    ((continuous_subtype_val.matrix_elem 0 1).pow t) |>.mul
    ((continuous_subtype_val.matrix_elem 1 1).pow u)

theorem entryMonomial_sphere (r s t u : ℕ) (g : SU2) :
    entryMonomial r s t u g = (-1 : ℂ)^t * sphereMonomial r u s t (su2ToSphere g) := by
  rw [entryMonomial, (su2_entries g).1, (su2_entries g).2]
  change g.val 0 0 ^ r * g.val 1 0 ^ s * (-star (g.val 1 0))^t * star (g.val 0 0)^u =
    (-1 : ℂ)^t * (g.val 0 0 ^ r * star (g.val 0 0)^u * g.val 1 0^s * star (g.val 1 0)^t)
  rw [neg_pow]
  ring

theorem entryMonomial_integral_left_zero (r s t u : ℕ) (h : r+t ≠ u+s) :
    (∫ g : SU2, entryMonomial r s t u g ∂normalizedHaar SU2) = 0 := by
  simp_rw [entryMonomial_sphere]
  rw [integral_const_mul, su2_firstColumn_integral (continuous_sphereMonomial r u s t),
    sphereMonomial_integral_zero r u s t h, mul_zero]

theorem entryMonomial_integral_diagonal (r s : ℕ) :
    (∫ g : SU2, entryMonomial r s s r g ∂normalizedHaar SU2) =
      (-1 : ℂ)^s * ((r.factorial : ℂ) * s.factorial / (r+s+1).factorial) := by
  simp_rw [entryMonomial_sphere]
  rw [integral_const_mul, su2_firstColumn_integral (continuous_sphereMonomial r r s s)]
  rw [← mixedMoment, mixedMoment_factorial]

/-- The monomial specialization required by the counterexample. -/
theorem balanced_entry_integral (r s t : ℕ) :
    (∫ g : SU2, entryMonomial r s t r g ∂normalizedHaar SU2) =
      if s = t then (-1 : ℂ)^s * ((r.factorial : ℂ) * s.factorial / (r+s+1).factorial) else 0 := by
  split_ifs with h
  · subst t; exact entryMonomial_integral_diagonal r s
  · exact entryMonomial_integral_left_zero r s t r (by omega)

theorem su2_determinant_relation (g : SU2) :
    g.val 0 0 * g.val 1 1 - g.val 1 0 * g.val 0 1 = 1 := by
  have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  simpa [Matrix.det_fin_two, mul_comm] using h

end XZMathieuSU2Counterexamples.Hopf
