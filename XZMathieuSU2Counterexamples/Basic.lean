import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-! Definition 2.1 and elementary witness logic. -/

namespace XZMathieuSU2Counterexamples

variable {K A B : Type*} [Field K] [CommRing A] [Algebra K A]
  [CommRing B] [Algebra K B]

/-- The manuscript's Mathieu condition, with natural positive exponents. -/
def IsMathieuSubspace (M : Submodule K A) : Prop :=
  ∀ f : A, (∀ m : ℕ, 1 ≤ m → f ^ m ∈ M) →
    ∀ h : A, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → h * f ^ m ∈ M

/-- A single fixed multiplier detecting every positive power refutes the condition. -/
theorem not_isMathieuSubspace_of_witness (M : Submodule K A) (f h : A)
    (hpure : ∀ m : ℕ, 1 ≤ m → f ^ m ∈ M)
    (hmarked : ∀ m : ℕ, 1 ≤ m → h * f ^ m ∉ M) :
    ¬ IsMathieuSubspace M := by
  intro hM
  obtain ⟨N, hN⟩ := hM f hpure h
  exact hmarked (max N 1) (le_max_right _ _) (hN _ (le_max_left _ _))

/-- The condition is inherited by the inverse image under an algebra homomorphism. -/
theorem IsMathieuSubspace.comap {M : Submodule K B} (hM : IsMathieuSubspace M)
    (φ : A →ₐ[K] B) : IsMathieuSubspace (M.comap φ.toLinearMap) := by
  intro f hf h
  obtain ⟨N, hN⟩ := hM (φ f) (by simpa using hf) (φ h)
  exact ⟨N, fun m hm => by simpa using hN m hm⟩

/-- A compatible functional transports a witness along an algebra homomorphism.
For quotient pullback the homomorphism goes from functions on the quotient to
functions on the source. Existence of that homomorphism is a separate obligation. -/
theorem counterexample_pullback (φ : A →ₐ[K] B) (I : A →ₗ[K] K) (J : B →ₗ[K] K)
    (hcompat : ∀ f, J (φ f) = I f) (f h : A)
    (hpure : ∀ m : ℕ, 1 ≤ m → I (f ^ m) = 0)
    (hmarked : ∀ m : ℕ, 1 ≤ m → I (h * f ^ m) ≠ 0) :
    ¬ IsMathieuSubspace (LinearMap.ker J) := by
  apply not_isMathieuSubspace_of_witness _ (φ f) (φ h)
  · intro m hm
    change J (φ f ^ m) = 0
    rw [← map_pow, hcompat]
    exact hpure m hm
  · intro m hm
    change J (φ h * φ f ^ m) ≠ 0
    rw [← map_pow, ← map_mul, hcompat]
    exact hmarked m hm

end XZMathieuSU2Counterexamples
