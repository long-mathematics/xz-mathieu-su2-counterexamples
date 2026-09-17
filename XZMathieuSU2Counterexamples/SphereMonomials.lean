import XZMathieuSU2Counterexamples.SU2Orbit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Phase cancellation and homogeneous scaled SU(2) identities for coordinate monomials. -/

noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples.Hopf

theorem normSq_phase (r θ : ℝ) :
    Complex.normSq ((r : ℂ) * Complex.exp (Complex.I * θ)) = r ^ 2 := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  simp [Complex.normSq_eq_norm_sq, Complex.norm_exp, pow_two]

def diagonalPhase (θ : ℝ) : SU2 := sphereToSU2 ⟨(Complex.exp (Complex.I * θ), 0), by
  simpa [a] using normSq_phase 1 θ⟩

theorem diagonalPhase_smul (θ : ℝ) (z : Sphere) :
    (diagonalPhase θ • z).val =
      (Complex.exp (Complex.I * θ) * z.val.1,
        star (Complex.exp (Complex.I * θ)) * z.val.2) := by
  simp [su2_smul_val, su2_smul_apply, diagonalPhase, sphereToSU2, sphereMatrix]

def coordinateMonomial (α β γ δ : ℕ) (z : Space) : ℂ :=
  z.1 ^ α * star z.1 ^ β * z.2 ^ γ * star z.2 ^ δ

def sphereMonomial (α β γ δ : ℕ) (z : Sphere) : ℂ :=
  coordinateMonomial α β γ δ z.val

@[fun_prop] theorem continuous_sphereMonomial (α β γ δ : ℕ) :
    Continuous (sphereMonomial α β γ δ) := by unfold sphereMonomial coordinateMonomial; fun_prop

theorem sphereMonomial_phase (α β γ δ : ℕ) (θ : ℝ) (z : Sphere) :
    sphereMonomial α β γ δ (diagonalPhase θ • z) =
      Complex.exp (((α : ℂ) + δ - β - γ) * Complex.I * θ) * sphereMonomial α β γ δ z := by
  have hc : star (Complex.exp (Complex.I * θ)) = Complex.exp (-Complex.I * θ) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  have hpow : Complex.exp (Complex.I * θ) ^ (α + δ) *
      star (Complex.exp (Complex.I * θ)) ^ (β + γ) =
      Complex.exp (((α : ℂ) + δ - β - γ) * Complex.I * θ) := by
    rw [hc, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hpow]
  simp only [sphereMonomial, coordinateMonomial, diagonalPhase_smul, mul_pow, star_mul, star_star, pow_add]
  ring

theorem sphereMonomial_integral_zero (α β γ δ : ℕ) (h : α + δ ≠ β + γ) :
    (∫ z, sphereMonomial α β γ δ z ∂surfaceMeasure) = 0 := by
  let n : ℝ := (α : ℝ) + δ - β - γ
  have hn : n ≠ 0 := by
    dsimp [n]
    intro hn
    have heq : (α : ℝ) + δ = β + γ := by linarith
    exact h (by exact_mod_cast heq)
  have hfreq : ((α : ℂ) + δ - β - γ) * Complex.I * ((Real.pi / n : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I := by
    have hnc : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    have hc : (n : ℂ) = (α : ℂ) + δ - β - γ := by simp [n]
    rw [← hc, Complex.ofReal_div]
    field_simp
  have heq := integral_smul_eq_self (μ := surfaceMeasure)
    (sphereMonomial α β γ δ) (g := diagonalPhase (Real.pi / n))
  simp_rw [sphereMonomial_phase, hfreq, Complex.exp_pi_mul_I] at heq
  rw [integral_const_mul] at heq
  linear_combination -heq / 2

theorem coordinateMonomial_real_smul (α β γ δ : ℕ) (r : ℝ) (z : Space) :
    coordinateMonomial α β γ δ ((r : ℂ) • z) =
      (r : ℂ) ^ (α + β + γ + δ) * coordinateMonomial α β γ δ z := by
  simp only [coordinateMonomial, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, star_mul,
    Complex.star_def, Complex.conj_ofReal, mul_pow, pow_add]
  ring

/-- The matrix formula also makes sense before normalizing its first column. -/
def scaledSU2Action (v z : Space) : Space :=
  (v.1 * z.1 - star v.2 * z.2, v.2 * z.1 + star v.1 * z.2)

theorem scaledSU2Action_real_smul (r : ℝ) (v z : Space) :
    scaledSU2Action ((r : ℂ) • v) z = (r : ℂ) • scaledSU2Action v z := by
  ext <;> simp [scaledSU2Action] <;> ring

theorem scaledSU2Action_unit (w : Sphere) (z : Space) :
    scaledSU2Action w.val z = sphereToSU2 w • z := by
  simp [scaledSU2Action, su2_smul_apply, sphereToSU2, sphereMatrix, sub_eq_add_neg]

theorem coordinateMonomial_scaled_integral_zero (α β γ δ : ℕ)
    (h : α + δ ≠ β + γ) (v : Space) :
    (∫ z : Sphere, coordinateMonomial α β γ δ (scaledSU2Action v z.val) ∂surfaceMeasure) = 0 := by
  obtain ⟨r, _hr, w, hv, _hr2⟩ := exists_radial_direction v
  simp_rw [hv, scaledSU2Action_real_smul, coordinateMonomial_real_smul,
    scaledSU2Action_unit]
  rw [integral_const_mul]
  change (r : ℂ) ^ (α + β + γ + δ) *
    (∫ z, sphereMonomial α β γ δ (sphereToSU2 w • z) ∂surfaceMeasure) = 0
  rw [integral_smul_eq_self, sphereMonomial_integral_zero α β γ δ h, mul_zero]

end XZMathieuSU2Counterexamples.Hopf

/- Adapted from MathieuProperty/SphereMonomials.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
