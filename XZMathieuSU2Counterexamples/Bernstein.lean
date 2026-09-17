import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic

/-! Beta/Bernstein and Laurent telescoping proofs adapted from the MIT-licensed
MathieuProperty/EarlierXZ.lean, reference d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics. See LICENSE. -/

noncomputable section
open MeasureTheory Polynomial
namespace XZMathieuSU2Counterexamples

theorem bernstein_integral (m j : ℕ) (hj : j ≤ m) :
    ∫ t in (0 : ℝ)..1, (m.choose j : ℂ) * (t : ℂ) ^ j * (1 - (t : ℂ)) ^ (m - j) =
      1 / (m + 1 : ℂ) := by
  have hb : (∫ t in (0 : ℝ)..1, (t : ℂ) ^ j * (1 - (t : ℂ)) ^ (m - j)) =
      Complex.betaIntegral (j + 1) (m - j + 1 : ℕ) := by
    unfold Complex.betaIntegral
    congr 1
    funext t
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Complex.cpow_natCast]
  have hs : (j + 1 : ℂ) + (m - j + 1 : ℕ) = ((m + 1 : ℕ) + 1 : ℂ) := by
    push_cast
    rw [Nat.cast_sub hj]
    ring
  have hfac : (m.choose j : ℂ) * j.factorial * (m - j).factorial = m.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  simp_rw [mul_assoc (m.choose j : ℂ)]
  rw [intervalIntegral.integral_const_mul, hb,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simp; positivity) (by simp; positivity), hs]
  simp only [Nat.cast_add, Nat.cast_one, Complex.Gamma_nat_eq_factorial]
  have hg : Complex.Gamma ((m : ℂ) + 1 + 1) = ((m + 1).factorial : ℂ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.Gamma_nat_eq_factorial (m + 1)
  rw [hg]
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  exact hfac

abbrev ScalarLaurent := LaurentPolynomial ℂ

def xzA : ScalarLaurent := 1 - LaurentPolynomial.T (-1)
def xzFamily (t : ℂ) : ScalarLaurent :=
  xzA * (LaurentPolynomial.C t * LaurentPolynomial.T 1 + LaurentPolynomial.C (1 - t))

theorem xzFamily_pow (t : ℂ) (m : ℕ) :
    xzFamily t ^ m = ∑ j ∈ Finset.range (m + 1),
      LaurentPolynomial.C ((m.choose j : ℂ) * t ^ j * (1 - t) ^ (m - j)) *
        (xzA ^ m * LaurentPolynomial.T (j : ℤ)) := by
  rw [xzFamily, mul_pow, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_pow, LaurentPolynomial.T_pow, mul_one, map_mul, map_pow, map_natCast]
  ring

theorem scalarLaurent_C_mul_coeff (c : ℂ) (f : ScalarLaurent) (k : ℤ) :
    (LaurentPolynomial.C c * f).coeff k = c * f.coeff k := by
  change (AddMonoidAlgebra.single 0 c * f).coeff k = _
  rw [AddMonoidAlgebra.coeff_single_mul_apply]
  simp

theorem xzFamily_integrated_coeff (m : ℕ) (k : ℤ) :
    ∫ t in (0 : ℝ)..1, (xzFamily (t : ℂ) ^ m).coeff k =
      (1 / (m + 1 : ℂ)) * (xzA ^ m * ∑ j ∈ Finset.range (m + 1), LaurentPolynomial.T (j : ℤ)).coeff k := by
  simp_rw [xzFamily_pow, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, scalarLaurent_C_mul_coeff]
  rw [intervalIntegral.integral_finsetSum (μ := volume)]
  · simp_rw [intervalIntegral.integral_mul_const]
    rw [Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [bernstein_integral m j (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  · intro j _
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (m.choose j : ℂ) * (t : ℂ)^j * (1 - (t : ℂ))^(m-j) *
        (xzA^m * LaurentPolynomial.T (j : ℤ)).coeff k)).intervalIntegrable (μ := volume) 0 1

theorem scalarLaurent_mul_T_coeff (f : ScalarLaurent) (i k : ℤ) :
    (f * LaurentPolynomial.T i).coeff k = f.coeff (k - i) := by
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

theorem xzA_pow_coeff_succ (m : ℕ) (k : ℤ) :
    (xzA ^ (m + 1)).coeff k = (xzA ^ m).coeff k - (xzA ^ m).coeff (k + 1) := by
  rw [pow_succ, xzA, mul_sub, mul_one, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    scalarLaurent_mul_T_coeff]
  rfl

theorem xzA_pow_coeff_outside (m : ℕ) (k : ℤ) (hk : k < -(m : ℤ) ∨ 0 < k) :
    (xzA ^ m).coeff k = 0 := by
  induction m generalizing k with
  | zero =>
    have hk0 : k ≠ 0 := by omega
    change (LaurentPolynomial.T (0 : ℤ) : ScalarLaurent).coeff k = 0
    rw [LaurentPolynomial.T_apply, ite_eq_right (Ne.symm hk0)]
  | succ m ih =>
    rw [xzA_pow_coeff_succ, ih k (by omega), ih (k + 1) (by omega), sub_self]

theorem xzA_pow_coeff_bottom (m : ℕ) : (xzA ^ m).coeff (-(m : ℤ)) = (-1 : ℂ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [xzA_pow_coeff_succ, xzA_pow_coeff_outside m _ (Or.inl (by omega))]
    have hk : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by omega
    rw [hk, ih, pow_succ]
    ring

theorem xzA_geometric_sum (m : ℕ) :
    xzA * ∑ j ∈ Finset.range (m + 1), (LaurentPolynomial.T (j : ℤ) : ScalarLaurent) =
      LaurentPolynomial.T (m : ℤ) - LaurentPolynomial.T (-1) := by
  induction m with
  | zero => simp [xzA]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hh : (LaurentPolynomial.T (-1) : ScalarLaurent) * LaurentPolynomial.T ((m + 1 : ℕ) : ℤ) =
        LaurentPolynomial.T (m : ℤ) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      omega
    rw [xzA, sub_mul, one_mul, hh]
    ring

theorem xzFamily_integral_pure (m : ℕ) (hm : 1 ≤ m) :
    ∫ t in (0 : ℝ)..1, (xzFamily (t : ℂ) ^ m).coeff 0 = 0 := by
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  rw [xzFamily_integrated_coeff, pow_succ, mul_assoc, xzA_geometric_sum,
    mul_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  simp only [scalarLaurent_mul_T_coeff]
  rw [xzA_pow_coeff_outside l _ (Or.inl (by omega)),
    xzA_pow_coeff_outside l _ (Or.inr (by omega)), sub_self, mul_zero]

theorem xzFamily_integral_marked (m : ℕ) (hm : 1 ≤ m) :
    ∫ t in (0 : ℝ)..1, (xzFamily (t : ℂ) ^ m).coeff 1 = (-1 : ℂ) ^ (m - 1) / (m + 1 : ℂ) := by
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  rw [xzFamily_integrated_coeff, pow_succ, mul_assoc, xzA_geometric_sum,
    mul_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  simp only [scalarLaurent_mul_T_coeff]
  rw [xzA_pow_coeff_outside l (1 - -1) (Or.inr (by omega))]
  have hk : (1 : ℤ) - (l + 1 : ℕ) = -(l : ℤ) := by omega
  rw [hk, xzA_pow_coeff_bottom]
  simp [div_eq_mul_inv, mul_comm]


/-- The exact Bernstein average, for every complex value of the Laurent variable. -/
theorem bernstein_average (n : ℕ) (z : ℂ) :
    (∫ x in (0 : ℝ)..1, ((1-(x : ℂ)) + (x : ℂ)*z)^n) =
      (1/(n+1 : ℂ)) * ∑ k ∈ Finset.range (n+1), z^k := by
  have he (x : ℝ) : ((1-(x : ℂ))+(x : ℂ)*z)^n =
      ∑ k ∈ Finset.range (n+1),
        ((n.choose k : ℂ)*(x : ℂ)^k*(1-(x : ℂ))^(n-k))*z^k := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_mul_const]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [bernstein_integral n k (by have := Finset.mem_range.mp hk; omega)]
  · intro k _
    exact (by fun_prop : Continuous (fun x : ℝ =>
      ((n.choose k : ℂ)*(x : ℂ)^k*(1-(x : ℂ))^(n-k))*z^k)).intervalIntegrable 0 1

end XZMathieuSU2Counterexamples
