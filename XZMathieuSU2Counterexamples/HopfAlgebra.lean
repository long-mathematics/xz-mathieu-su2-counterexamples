import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! The quadratic unit sphere in two complex coordinates. -/

namespace XZMathieuSU2Counterexamples.Hopf

abbrev Space := ℂ × ℂ

def a (z : Space) : ℝ := Complex.normSq z.1 + Complex.normSq z.2
def Sphere := {z : Space // a z = 1}

theorem a_nonneg (z : Space) : 0 ≤ a z :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem a_eq_zero_iff (z : Space) : a z = 0 ↔ z = 0 := by
  simp only [a, add_eq_zero_iff_of_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _),
    Complex.normSq_eq_zero, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]

theorem a_smul (c : ℂ) (z : Space) : a (c • z) = Complex.normSq c * a z := by
  simp [a, Complex.normSq_mul, mul_add]


end XZMathieuSU2Counterexamples.Hopf

/- Adapted from MathieuProperty/HopfAlgebra.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
