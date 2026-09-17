import XZMathieuSU2Counterexamples.LaurentIntegral

noncomputable section
open MeasureTheory Polynomial
namespace XZMathieuSU2Counterexamples

def basic : Laurent := (1 - LaurentPolynomial.T (-1)) *
  (LaurentPolynomial.C (1 - X) + LaurentPolynomial.C X * LaurentPolynomial.T 1)

theorem basic_specialize (x : ℂ) : specialize x basic = xzFamily x := by
  simp [basic, xzFamily, xzA, add_comm]

theorem basic_pure (n : ℕ) (hn : 1 ≤ n) : integral (basic ^ n) = 0 := by
  unfold integral
  simp_rw [← specialize_coeff, map_pow, basic_specialize]
  exact xzFamily_integral_pure n hn

theorem basic_marked (n : ℕ) (hn : 1 ≤ n) :
    integral (LaurentPolynomial.T (-1) * basic ^ n) = (-1 : ℂ) ^ (n-1) / (n+1) := by
  unfold integral
  have he : (LaurentPolynomial.T (-1) * basic ^ n).coeff 0 = (basic ^ n).coeff 1 := by
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
    rfl
  rw [he]
  simp_rw [← specialize_coeff, map_pow, basic_specialize]
  exact xzFamily_integral_marked n hn

theorem basic_marked_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    integral (LaurentPolynomial.T (-1) * basic ^ n) ≠ 0 := by
  rw [basic_marked n hn]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.succ_ne_zero n)

theorem basic_expansion : basic =
    LaurentPolynomial.C (X - 1) * LaurentPolynomial.T (-1) +
    LaurentPolynomial.C (1 - 2 * X) +
    LaurentPolynomial.C (X) * LaurentPolynomial.T 1 := by
  have ht : (LaurentPolynomial.T (-1) : Laurent) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  simp only [basic, map_sub, map_one, map_mul, map_ofNat]
  linear_combination -LaurentPolynomial.C (X) * ht

theorem basic_coeff (k : ℤ) : basic.coeff k =
    (if k = -1 then X - 1 else 0) +
    (if k = 0 then 1 - 2 * X else 0) +
    (if k = 1 then X else 0) := by
  rw [basic_expansion]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    LaurentPolynomial.C_apply, Finsupp.single_apply]
  simp [eq_comm]

theorem basic_spectrum : basic.coeff.support = {-1, 0, 1} := by
  classical
  have hneg : (X - 1 : ℂ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (2 : ℂ)) h
    norm_num at hh
  have hzero : (1 - 2 * X : ℂ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (2 : ℂ)) h
    norm_num at hh
  ext k
  simp only [Finsupp.mem_support_iff, basic_coeff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hkneg : k = -1
  · subst k; simpa using hneg
  by_cases hkzero : k = 0
  · subst k; simpa using hzero
  by_cases hkpos : k = 1
  · subst k; simp
  · simp [hkneg, hkzero, hkpos]


theorem basic_zero_mem_convexHull : (0 : ℝ) ∈
    convexHull ℝ ((fun k : ℤ => (k : ℝ)) '' (basic.coeff.support : Set ℤ)) := by
  apply subset_convexHull ℝ
  exact ⟨0, by simp [basic_spectrum], by simp⟩

theorem not_XZConjecture : ¬ XZConjecture := by
  intro h
  exact h basic basic_pure basic_zero_mem_convexHull

theorem kernel_not_mathieu : ¬ IsMathieuSubspace (LinearMap.ker integralLinear) :=
  not_isMathieuSubspace_of_witness _ basic (LaurentPolynomial.T (-1))
    basic_pure basic_marked_ne_zero

/-- Theorem 2.1, including its exact spectrum and both stated consequences. -/
theorem basic_xz :
    (∀ n : ℕ, 1 ≤ n → integral (basic ^ n) = 0) ∧
    (∀ n : ℕ, 1 ≤ n → integral (LaurentPolynomial.T (-1) * basic ^ n) =
      (-1 : ℂ) ^ (n-1) / (n+1)) ∧
    basic.coeff.support = {-1,0,1} ∧ ¬ XZConjecture ∧
    ¬ IsMathieuSubspace (LinearMap.ker integralLinear) :=
  ⟨basic_pure, basic_marked, basic_spectrum, not_XZConjecture, kernel_not_mathieu⟩

end XZMathieuSU2Counterexamples
