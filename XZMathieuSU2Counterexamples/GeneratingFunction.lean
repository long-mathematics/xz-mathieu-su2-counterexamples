import XZMathieuSU2Counterexamples.XZWitness
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
open Polynomial
namespace XZMathieuSU2Counterexamples

theorem alternating_row (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n+1), (-1 : ℂ)^k * n.choose k) = 0 := by
  exact_mod_cast Int.alternating_sum_range_choose_of_ne (n := n) (by omega)

theorem alternating_partial_row (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range n, (-1 : ℂ)^k * n.choose k) = (-1 : ℂ)^(n-1) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  have h := Int.alternating_sum_range_choose_eq_choose (n := m) (m := m)
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.add_sub_cancel] at h ⊢
  exact_mod_cast h

/-- Coefficientwise moment generating series; its degree-zero moment is included. -/
def momentSeries : PowerSeries ℂ := PowerSeries.mk (fun n => integral (basic^n))

theorem momentSeries_eq_one : momentSeries = 1 := by
  ext n
  simp only [momentSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  cases n with
  | zero => simp [integral]
  | succ n => simp [basic_pure (n+1) (by omega)]

/-- The exact radicand simplification in Remark 2.3. -/
theorem generating_radicand (x t : ℂ) :
    (1-t*(1-2*x))^2 + 4*t^2*x*(1-x) = (1-t)^2 + 4*t*x := by ring

/-- The cancellation identity displayed in Section 5. -/
theorem cancellation_mechanism (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n+1), (-1 : ℂ)^k * n.choose k) = 0 ∧
    (∑ k ∈ Finset.range n, (-1 : ℂ)^k * n.choose k) = (-1 : ℂ)^(n-1) ∧
    integral (basic^n) = 0 ∧ integral (LaurentPolynomial.T (-1) * basic^n) ≠ 0 :=
  ⟨alternating_row n hn, alternating_partial_row n hn, basic_pure n hn, basic_marked_ne_zero n hn⟩

end XZMathieuSU2Counterexamples
