import XZMathieuSU2Counterexamples.SU2Integration

noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples.Hopf

open MvPolynomial in
def FPolynomial (lam μ : ℂ) : TriplePolynomial :=
  C lam * (1 + C μ * X 2) * (X 0 + C μ⁻¹ * X 1)

open MvPolynomial in
def GPolynomial : TriplePolynomial := -X 2

def su2F (lam μ : ℂ) : representativeFunctions (G := SU2) := entryTriple (FPolynomial lam μ)
def su2G : representativeFunctions (G := SU2) := entryTriple GPolynomial

/-- The exact coordinate-entry function of Theorem 4.2. -/
theorem su2F_apply (lam μ : ℂ) (g : SU2) :
    (su2F lam μ).val g = lam * (1 + μ * g.val 0 1) *
      (g.val 0 0 * g.val 1 1 + μ⁻¹ * g.val 1 0) := by
  simp [su2F, FPolynomial, entryTriple]

theorem su2G_apply (g : SU2) : su2G.val g = -g.val 0 1 := by
  simp [su2G, GPolynomial, entryTriple]

theorem betaTriple_F (lam μ : ℂ) : betaTriple (FPolynomial lam μ) = circuit 1 lam μ := by
  simp only [FPolynomial, betaTriple, map_mul, map_add, map_one,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  change LaurentPolynomial.C (Polynomial.C lam) *
    (1 + LaurentPolynomial.C (Polynomial.C μ) * (-LaurentPolynomial.T (-1))) *
    (LaurentPolynomial.C (1-Polynomial.X) + LaurentPolynomial.C (Polynomial.C μ⁻¹) *
      (LaurentPolynomial.C Polynomial.X * LaurentPolynomial.T 1)) = _
  simp only [circuit, map_mul]
  ring

theorem betaTriple_G : betaTriple GPolynomial = LaurentPolynomial.T (-1) := by
  simp [GPolynomial, betaTriple]

theorem su2_pure (lam μ : ℂ) (hμ : μ ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    representativeIntegral SU2 (su2F lam μ ^ n) = 0 := by
  rw [su2F, ← map_pow, su2_polynomial_transfer, map_pow, betaTriple_F]
  exact circuit_pure 1 (by omega) lam μ hμ n hn

theorem su2_marked (lam μ : ℂ) (hμ : μ ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    representativeIntegral SU2 (su2G * su2F lam μ ^ n) =
      (-1 : ℂ)^(n-1) * lam^n * μ⁻¹ / (n+1) := by
  rw [su2G, su2F, ← map_pow, ← map_mul, su2_polynomial_transfer,
    map_mul, map_pow, betaTriple_G, betaTriple_F]
  exact circuit_marked 1 (by omega) lam μ hμ n hn

theorem su2_marked_ne_zero (lam μ : ℂ) (hlam : lam ≠ 0) (hμ : μ ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) : representativeIntegral SU2 (su2G * su2F lam μ ^ n) ≠ 0 := by
  rw [su2_marked lam μ hμ n hn]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ hlam)) (inv_ne_zero hμ)) (by exact_mod_cast Nat.succ_ne_zero n)

/-- The actual representative-algebra Mathieu property fails on SU(2). -/
theorem SU2_not_mathieu : ¬ HasMathieuProperty SU2 :=
  not_mathieu_of_representative_witness SU2 (su2F 1 1) su2G
    (su2_pure 1 1 one_ne_zero) (su2_marked_ne_zero 1 1 one_ne_zero one_ne_zero)

/-- Theorem 4.2 on actual determinant-one unitary matrices and normalized Haar measure. -/
theorem su2_counterexample (lam μ : ℂ) (hlam : lam ≠ 0) (hμ : μ ≠ 0) :
    (∀ n : ℕ, 1 ≤ n →
      (∫ g : SU2, (lam * (1+μ*g.val 0 1) *
        (g.val 0 0*g.val 1 1 + μ⁻¹*g.val 1 0))^n ∂normalizedHaar SU2) = 0) ∧
    (∀ n : ℕ, 1 ≤ n →
      (∫ g : SU2, (lam * (1+μ*g.val 0 1) *
        (g.val 0 0*g.val 1 1 + μ⁻¹*g.val 1 0))^n * (-g.val 0 1) ∂normalizedHaar SU2) =
          (-1 : ℂ)^(n-1) * lam^n * μ⁻¹ / (n+1)) ∧
    (∀ n : ℕ, 1 ≤ n → (-1 : ℂ)^(n-1) * lam^n * μ⁻¹ / (n+1) ≠ 0) ∧
    ¬ HasMathieuProperty SU2 := by
  refine ⟨?_, ?_, ?_, SU2_not_mathieu⟩
  · intro n hn
    have h := su2_pure lam μ hμ n hn
    change (∫ g : SU2, (su2F lam μ).val g ^ n ∂normalizedHaar SU2) = 0 at h
    simpa only [su2F_apply] using h
  · intro n hn
    have h := su2_marked lam μ hμ n hn
    change (∫ g : SU2, su2G.val g * (su2F lam μ).val g ^ n ∂normalizedHaar SU2) = _ at h
    simpa only [su2F_apply, su2G_apply, mul_comm] using h
  · intro n hn
    have h := su2_marked_ne_zero lam μ hlam hμ n hn
    rwa [su2_marked lam μ hμ n hn] at h

/-- The especially small pair stated in the abstract. -/
theorem small_pair (n : ℕ) (hn : 1 ≤ n) :
    (∫ g : SU2, ((1+g.val 0 1) * (g.val 0 0*g.val 1 1+g.val 1 0))^n ∂normalizedHaar SU2) = 0 ∧
    (∫ g : SU2, ((1+g.val 0 1) * (g.val 0 0*g.val 1 1+g.val 1 0))^n * (-g.val 0 1)
      ∂normalizedHaar SU2) = (-1 : ℂ)^(n-1)/(n+1) := by
  have h := su2_counterexample 1 1 one_ne_zero one_ne_zero
  exact ⟨by simpa using h.1 n hn, by simpa using h.2.1 n hn⟩

end XZMathieuSU2Counterexamples.Hopf
