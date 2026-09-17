import XZMathieuSU2Counterexamples.XZWitness

noncomputable section
open Polynomial
namespace XZMathieuSU2Counterexamples

local notation "LC" => LaurentPolynomial.C
local notation "LT" => LaurentPolynomial.T

def circuit (d : ℤ) (lam μ : ℂ) : Laurent :=
  LC (C lam) * (1 - LC (C μ) * LT (-d)) *
    (LC (1-X) + LC (X * C μ⁻¹) * LT d)

def circuitMonomial (d : ℤ) (μ : ℂ) (hμ : μ ≠ 0) : Multiplicative ℤ →* Laurent where
  toFun k := LC (C (μ ^ (-k.toAdd))) * LT (d * k.toAdd)
  map_one' := by simp
  map_mul' i j := by
    change LC (C (μ ^ (-(i.toAdd + j.toAdd)))) * LT (d * (i.toAdd + j.toAdd)) = _
    simp only [neg_add, zpow_add₀ hμ, map_mul, mul_add]
    rw [LaurentPolynomial.T_add]
    ring

def circuitMap (d : ℤ) (μ : ℂ) (hμ : μ ≠ 0) : Laurent →+* Laurent :=
  AddMonoidAlgebra.liftNCRingHom LC (circuitMonomial d μ hμ) (fun _ _ => Commute.all _ _)

theorem circuitMap_single (d k : ℤ) (μ : ℂ) (hμ : μ ≠ 0) (p : ℂ[X]) :
    circuitMap d μ hμ (LC p * LT k) = LC (p * C (μ ^ (-k))) * LT (d*k) := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  rw [circuitMap, AddMonoidAlgebra.liftNCRingHom_single]
  change LC p * (LC (C (μ ^ (-k))) * LT (d*k)) = _
  rw [map_mul, mul_assoc]

theorem circuitMap_C (d : ℤ) (μ : ℂ) (hμ : μ ≠ 0) (p : ℂ[X]) :
    circuitMap d μ hμ (LC p) = LC p := by
  simpa using circuitMap_single d 0 μ hμ p

theorem circuitMap_T (d k : ℤ) (μ : ℂ) (hμ : μ ≠ 0) :
    circuitMap d μ hμ (LT k) = LC (C (μ ^ (-k))) * LT (d*k) := by
  simpa using circuitMap_single d k μ hμ 1

theorem circuitMap_coeff (d : ℤ) (hd : d ≠ 0) (μ : ℂ) (hμ : μ ≠ 0)
    (f : Laurent) (k : ℤ) :
    (circuitMap d μ hμ f).coeff (d*k) = f.coeff k * C (μ ^ (-k)) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg, add_mul]
  | C_mul_T j p =>
    rw [circuitMap_single]
    simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, mul_eq_mul_left_iff, hd, or_false]
    split_ifs with h
    · subst j; rfl
    · simp

theorem circuit_eq_map (d : ℤ) (lam μ : ℂ) (hμ : μ ≠ 0) :
    circuit d lam μ = LC (C lam) * circuitMap d μ hμ basic := by
  simp [basic, circuit, circuitMap_C, circuitMap_T, map_mul]
  ring

theorem circuit_moment_coeff (d : ℤ) (hd : d ≠ 0) (lam μ : ℂ) (hμ : μ ≠ 0)
    (n : ℕ) (k : ℤ) :
    (circuit d lam μ ^ n).coeff (d*k) = C (lam^n * μ^(-k)) * (basic ^ n).coeff k := by
  rw [circuit_eq_map d lam μ hμ, mul_pow, ← map_pow, ← map_pow, ← map_pow]
  change (LC (C (lam ^ n)) * circuitMap d μ hμ (basic ^ n)).coeff (d*k) = _
  rw [show ∀ (p : ℂ[X]) (f : Laurent) (j : ℤ), (LC p * f).coeff j = p * f.coeff j from
    fun p f j => by
      change (AddMonoidAlgebra.single 0 p * f).coeff j = _
      rw [AddMonoidAlgebra.coeff_single_mul_apply]; simp]
  rw [circuitMap_coeff d hd μ hμ, map_mul]
  ring

theorem circuit_pure (d : ℤ) (hd : 1 ≤ d) (lam μ : ℂ) (hμ : μ ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) : integral (circuit d lam μ ^ n) = 0 := by
  have hc := circuit_moment_coeff d (by omega) lam μ hμ n 0
  simp only [mul_zero, neg_zero, zpow_zero, mul_one] at hc
  simp only [integral, hc, eval_mul, eval_C]
  rw [intervalIntegral.integral_const_mul]
  change lam ^ n * integral (basic ^ n) = 0
  rw [basic_pure n hn, mul_zero]

theorem circuit_marked (d : ℤ) (hd : 1 ≤ d) (lam μ : ℂ) (hμ : μ ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) :
    integral (LT (-d) * circuit d lam μ ^ n) = (-1 : ℂ)^(n-1) * lam^n * μ⁻¹ / (n+1) := by
  have hc := circuit_moment_coeff d (by omega) lam μ hμ n 1
  simp only [mul_one, zpow_neg_one] at hc
  have hs : (LT (-d) * circuit d lam μ ^ n).coeff 0 = (circuit d lam μ ^ n).coeff d := by
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul,
      add_zero, neg_neg]
  simp only [integral, hs, hc, eval_mul, eval_C]
  rw [intervalIntegral.integral_const_mul]
  have hb : (∫ x in (0 : ℝ)..1, ((basic ^ n).coeff 1).eval (x : ℂ)) =
      (-1 : ℂ)^(n-1)/(n+1) := by
    simp_rw [← specialize_coeff, map_pow, basic_specialize]
    exact xzFamily_integral_marked n hn
  rw [hb]
  ring

theorem circuit_expansion (d : ℤ) (lam μ : ℂ) (hμ : μ ≠ 0) :
    circuit d lam μ = LC (C (lam*μ⁻¹) * X) * LT d + LC (C lam * (1-2*X)) -
      LC (C (lam*μ) * (1-X)) * LT (-d) := by
  have ht : (LT (-d) : Laurent) * LT d = 1 := by rw [← LaurentPolynomial.T_add]; simp
  have hu : (LC (C μ) : Laurent) * LC (C μ⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hμ, map_one, map_one]
  simp only [circuit, map_mul, map_sub, map_one, map_ofNat]
  linear_combination -LC (C lam) * LC X * (LC (C μ) * LC (C μ⁻¹)) * ht -
    LC (C lam) * LC X * hu

theorem circuit_coeff (d k : ℤ) (lam μ : ℂ) (hμ : μ ≠ 0) :
    (circuit d lam μ).coeff k =
      (if k = d then C (lam*μ⁻¹) * X else 0) +
      (if k = 0 then C lam * (1-2*X) else 0) -
      (if k = -d then C (lam*μ) * (1-X) else 0) := by
  rw [circuit_expansion d lam μ hμ]
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, LaurentPolynomial.C_apply, Finsupp.single_apply]
  simp [eq_comm]

theorem circuit_spectrum (d : ℤ) (hd : 1 ≤ d) (lam μ : ℂ) (hlam : lam ≠ 0) (hμ : μ ≠ 0) :
    (circuit d lam μ).coeff.support = {-d,0,d} := by
  classical
  have hp : (C (lam*μ⁻¹) * X : ℂ[X]) ≠ 0 := by
    exact mul_ne_zero (by simpa using mul_ne_zero hlam (inv_ne_zero hμ)) X_ne_zero
  have hz : (C lam * (1-2*X) : ℂ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (0 : ℂ)) h
    simp [hlam] at hh
  have hn : (C (lam*μ) * (1-X) : ℂ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (0 : ℂ)) h
    simp [hlam, hμ] at hh
  ext k
  simp only [Finsupp.mem_support_iff, circuit_coeff d k lam μ hμ,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases hkd : k = d
  · subst k; simp [show d ≠ 0 by omega, show d ≠ -d by omega, hlam, hμ]
  by_cases hk0 : k = 0
  · subst k; simp [show (0 : ℤ) ≠ d by omega, show (0 : ℤ) ≠ -d by omega, hz]
  by_cases hkn : k = -d
  · subst k; simp [show -d ≠ d by omega, show -d ≠ 0 by omega]
    simpa using hn
  · simp [hkd, hk0, hkn]

theorem circuit_marked_ne_zero (d : ℤ) (hd : 1 ≤ d) (lam μ : ℂ)
    (hlam : lam ≠ 0) (hμ : μ ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    integral (LT (-d) * circuit d lam μ ^ n) ≠ 0 := by
  rw [circuit_marked d hd lam μ hμ n hn]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ hlam)) (inv_ne_zero hμ)) (by exact_mod_cast Nat.succ_ne_zero n)

/-- Proposition 3.1, preserving all three parameters and exact coefficients. -/
theorem circuit_family (d : ℤ) (hd : 1 ≤ d) (lam μ : ℂ) (hlam : lam ≠ 0) (hμ : μ ≠ 0) :
    (circuit d lam μ).coeff.support = {-d,0,d} ∧
    (∀ n : ℕ, 1 ≤ n → integral (circuit d lam μ ^ n) = 0) ∧
    (∀ n : ℕ, 1 ≤ n → integral (LT (-d) * circuit d lam μ ^ n) =
      (-1 : ℂ)^(n-1) * lam^n * μ⁻¹ / (n+1)) :=
  ⟨circuit_spectrum d hd lam μ hlam hμ, circuit_pure d hd lam μ hμ,
    circuit_marked d hd lam μ hμ⟩

end XZMathieuSU2Counterexamples
