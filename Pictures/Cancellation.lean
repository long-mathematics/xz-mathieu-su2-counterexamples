import XZMathieuSU2Counterexamples

/-!
# The cancellation mechanism, drawn in the infoview

An interactive picture of Section 5 of the manuscript, for VS Code (the Lean 4 extension) and Lean Studio:
put the cursor on the `#widget` line at the bottom of this file and open the infoview.

After the substitution of Lemma 4.1, `Fⁿ` becomes `(1 - z⁻¹)ⁿ ((1 - x) + x z)ⁿ`. By
`bernstein_average`, integrating out `x` gives every power `zᵏ` the same weight `1/(n+1)`, so the
constant term is the diagonal of a grid whose rows are the terms of `(1 - z⁻¹)ⁿ`: the full alternating
row, which is `0`. Multiplying by `G ↦ z⁻¹` moves the diagonal one step and drops the last term,
leaving `(-1)ⁿ⁻¹`.

The numbers the picture shows are not a separate computation. `pure_moment_eq_diagonal` and
`marked_moment_eq_diagonal` prove, for every `n ≥ 1`, that the project's integrals equal the drawn
diagonal sums divided by `n + 1`.

This file is editorial: it adds no manuscript obligation and is not part of the release audit.
Written with the assistance of Claude (Anthropic).
-/

namespace Pictures

open XZMathieuSU2Counterexamples Lean

/-- The coefficient of `z⁻ʲ` in `(1 - z⁻¹)ⁿ`: row `j` of the grid. -/
def rowCoeff (n j : ℕ) : ℤ := (-1) ^ j * (n.choose j : ℤ)

/-- The main diagonal `k = j`: the constant term of `Fⁿ`, times `n + 1`. -/
def pureDiagonal (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), rowCoeff n j

/-- The shifted diagonal `k = j + 1`: the constant term of `z⁻¹ Fⁿ`, times `n + 1`. -/
def markedDiagonal (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, rowCoeff n j

theorem pureDiagonal_cast (n : ℕ) :
    (pureDiagonal n : ℂ) = ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * n.choose k := by
  simp [pureDiagonal, rowCoeff]

theorem markedDiagonal_cast (n : ℕ) :
    (markedDiagonal n : ℂ) = ∑ k ∈ Finset.range n, (-1 : ℂ) ^ k * n.choose k := by
  simp [markedDiagonal, rowCoeff]

/-- The drawn main diagonal always sums to zero. -/
theorem pureDiagonal_eq (n : ℕ) (hn : 1 ≤ n) : pureDiagonal n = 0 := by
  have h : (pureDiagonal n : ℂ) = 0 := by rw [pureDiagonal_cast, alternating_row n hn]
  exact_mod_cast h

/-- The drawn shifted diagonal always sums to `(-1)ⁿ⁻¹`. -/
theorem markedDiagonal_eq (n : ℕ) (hn : 1 ≤ n) : markedDiagonal n = (-1) ^ (n - 1) := by
  have h : (markedDiagonal n : ℂ) = (-1) ^ (n - 1) := by
    rw [markedDiagonal_cast, alternating_partial_row n hn]
  exact_mod_cast h

/-- The pure moment of the manuscript's `f` is the drawn main diagonal over `n + 1`. -/
theorem pure_moment_eq_diagonal (n : ℕ) (hn : 1 ≤ n) :
    ∫ t in (0 : ℝ)..1, (xzFamily (t : ℂ) ^ n).coeff 0 = (pureDiagonal n : ℂ) / (n + 1) := by
  rw [xzFamily_integral_pure n hn, pureDiagonal_eq n hn]
  simp

/-- The mixed moment against `z⁻¹` is the drawn shifted diagonal over `n + 1`. -/
theorem marked_moment_eq_diagonal (n : ℕ) (hn : 1 ≤ n) :
    ∫ t in (0 : ℝ)..1, (xzFamily (t : ℂ) ^ n).coeff 1 = (markedDiagonal n : ℂ) / (n + 1) := by
  rw [xzFamily_integral_marked n hn, markedDiagonal_eq n hn]
  push_cast
  rfl

/-- Reduce `p / q` to lowest terms, for display. -/
def fracJson (p q : ℤ) : Json :=
  let g := (Int.gcd p q : ℤ)
  Json.arr #[toJson (p / g), toJson (q / g)]

def rowJson (n : ℕ) : Json :=
  json% {
    n: $(n),
    coeffs: $((List.range (n + 1)).toArray.map fun j => toJson (rowCoeff n j)),
    pure: $(fracJson (pureDiagonal n) (n + 1)),
    marked: $(fracJson (markedDiagonal n) (n + 1))
  }

/-- What the picture draws: exponents `n = 1, …, 8`, every number computed from the definitions above. -/
def props : Json :=
  json% {
    rows: $((List.range' 1 8).toArray.map rowJson),
    proved: $(#[
      "Hopf.small_pair: on SU(2), ∫ Fⁿ dg = 0 and ∫ Fⁿ·G dg = (−1)ⁿ⁻¹/(n+1), every n ≥ 1",
      "Pictures.pure_moment_eq_diagonal, Pictures.marked_moment_eq_diagonal: these are the drawn diagonals",
      "Hopf.SU2_not_mathieu: ¬ HasMathieuProperty SU2"])
  }

@[widget_module]
def Cancellation : Widget.Module where
  javascript := include_str "cancellation.js"

end Pictures

open Pictures in
#widget Cancellation with props
