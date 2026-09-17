import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Tactic

/-! Finite-dimensional continuous matrix representations and their coefficient algebra.
Continuity here concerns the group variable as well as the linear action. -/

noncomputable section

open scoped BigOperators Kronecker

namespace XZMathieuSU2Counterexamples

variable (G : Type*) [Monoid G] [TopologicalSpace G]

/-- A continuous complex representation in a finite coordinate basis. -/
structure MatrixRepresentation (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toMonoidHom : G →* Matrix ι ι ℂ
  continuous_entry : ∀ i j, Continuous fun g => toMonoidHom g i j

namespace MatrixRepresentation

variable {G} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A coordinate matrix coefficient, bundled as a continuous function. -/
def entry (ρ : MatrixRepresentation G ι) (i j : ι) : C(G, ℂ) :=
  ⟨fun g => ρ.toMonoidHom g i j, ρ.continuous_entry i j⟩

/-- Change of coordinate indexing preserves the representation. -/
def reindex (ρ : MatrixRepresentation G ι) (e : ι ≃ κ) : MatrixRepresentation G κ where
  toMonoidHom := (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom.comp ρ.toMonoidHom
  continuous_entry i j := ρ.continuous_entry (e.symm i) (e.symm j)

@[simp] theorem entry_reindex (ρ : MatrixRepresentation G ι) (e : ι ≃ κ) (i j : ι) :
    (ρ.reindex e).entry (e i) (e j) = ρ.entry i j := by
  ext g
  simp [entry, reindex, Matrix.reindex_apply]

/-- Tensor representation in the product basis, realized by the Kronecker product. -/
def tensor (ρ : MatrixRepresentation G ι) (σ : MatrixRepresentation G κ) :
    MatrixRepresentation G (ι × κ) where
  toMonoidHom :=
    { toFun := fun g => ρ.toMonoidHom g ⊗ₖ σ.toMonoidHom g
      map_one' := by simp
      map_mul' := by intro g h; simp [Matrix.mul_kronecker_mul] }
  continuous_entry i j := (ρ.continuous_entry i.1 j.1).mul (σ.continuous_entry i.2 j.2)

theorem entry_tensor (ρ : MatrixRepresentation G ι) (σ : MatrixRepresentation G κ)
    (i j : ι) (k l : κ) :
    (ρ.tensor σ).entry (i, k) (j, l) = ρ.entry i j * σ.entry k l := rfl

/-- The conjugate representation, using entrywise conjugation, not adjoint matrices. -/
def conjugate (ρ : MatrixRepresentation G ι) : MatrixRepresentation G ι where
  toMonoidHom := (starRingEnd ℂ).mapMatrix.toMonoidHom.comp ρ.toMonoidHom
  continuous_entry i j := (ρ.continuous_entry i j).star

theorem entry_conjugate (ρ : MatrixRepresentation G ι) (i j : ι) :
    ρ.conjugate.entry i j = star (ρ.entry i j) := rfl

variable {H : Type*} [Monoid H] [TopologicalSpace H]

/-- Restriction along a continuous homomorphism. -/
def pullback (ρ : MatrixRepresentation H ι) (π : G →* H) (hπ : Continuous π) :
    MatrixRepresentation G ι where
  toMonoidHom := ρ.toMonoidHom.comp π
  continuous_entry i j := (ρ.continuous_entry i j).comp hπ

theorem entry_pullback (ρ : MatrixRepresentation H ι) (π : G →* H) (hπ : Continuous π)
    (i j : ι) : (ρ.pullback π hπ).entry i j = (ρ.entry i j).comp ⟨π, hπ⟩ := rfl

/-- A coefficient with arbitrary covector and vector, expressed in coordinates.
The covector coordinates already include conjugation when it comes from an inner product. -/
def coefficient (ρ : MatrixRepresentation G ι) (a v : ι → ℂ) : C(G, ℂ) :=
  ∑ i, ∑ j, (a i * v j) • ρ.entry i j

theorem coefficient_apply (ρ : MatrixRepresentation G ι) (a v : ι → ℂ) (g : G) :
    ρ.coefficient a v g = ∑ i, ∑ j, a i * (ρ.toMonoidHom g i j) * v j := by
  simp [coefficient, entry, mul_assoc, mul_comm, mul_left_comm]

theorem coefficient_mul (ρ : MatrixRepresentation G ι) (σ : MatrixRepresentation G κ)
    (a v : ι → ℂ) (b w : κ → ℂ) :
    ρ.coefficient a v * σ.coefficient b w =
      (ρ.tensor σ).coefficient (fun p => a p.1 * b p.2) (fun p => v p.1 * w p.2) := by
  ext g
  simp only [ContinuousMap.mul_apply, coefficient_apply, tensor, MonoidHom.coe_mk,
    OneHom.coe_mk, Matrix.kronecker_apply, Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem coefficient_conj (ρ : MatrixRepresentation G ι) (a v : ι → ℂ) :
    star (ρ.coefficient a v) = ρ.conjugate.coefficient (star a) (star v) := by
  ext g
  simp [coefficient_apply, conjugate, mul_comm]

/-- The usual linear representation associated to a matrix representation. -/
def toRepresentation (ρ : MatrixRepresentation G ι) : Representation ℂ G (ι → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ.toMonoidHom

theorem continuous_orbit (ρ : MatrixRepresentation G ι) (v : ι → ℂ) :
    Continuous fun g => ρ.toRepresentation g v := by
  apply continuous_pi
  intro i
  change Continuous fun g => ∑ j, ρ.toMonoidHom g i j * v j
  exact continuous_finsetSum _ fun j _ => (ρ.continuous_entry i j).mul continuous_const

/-- Joint continuity of the action, not merely continuity of individual operators. -/
theorem continuous_action (ρ : MatrixRepresentation G ι) :
    Continuous fun p : G × (ι → ℂ) => ρ.toRepresentation p.1 p.2 := by
  apply continuous_pi
  intro i
  change Continuous fun p : G × (ι → ℂ) => ∑ j, ρ.toMonoidHom p.1 i j * p.2 j
  exact continuous_finsetSum _ fun j _ =>
    ((ρ.continuous_entry i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)

/-- The Kronecker model is exactly mathlib's tensor-product representation in the
tensor product of the coordinate bases. -/
theorem tensor_toMatrix (ρ : MatrixRepresentation G ι) (σ : MatrixRepresentation G κ) (g : G) :
    LinearMap.toMatrix ((Pi.basisFun ℂ ι).tensorProduct (Pi.basisFun ℂ κ))
      ((Pi.basisFun ℂ ι).tensorProduct (Pi.basisFun ℂ κ))
      (ρ.toRepresentation.tprod σ.toRepresentation g) = (ρ.tensor σ).toMonoidHom g := by
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  change LinearMap.toMatrix' (Matrix.toLin' (ρ.toMonoidHom g)) ⊗ₖ
    LinearMap.toMatrix' (Matrix.toLin' (σ.toMonoidHom g)) = _
  simp [tensor]

/-- Entrywise conjugation intertwines the original and conjugate actions. -/
theorem conjugate_action (ρ : MatrixRepresentation G ι) (g : G) (v : ι → ℂ) :
    ρ.conjugate.toRepresentation g (star v) = star (ρ.toRepresentation g v) := by
  ext i
  change (∑ j, star (ρ.toMonoidHom g i j) * star (v j)) =
    star (∑ j, ρ.toMonoidHom g i j * v j)
  simp

theorem entry_as_coefficient (ρ : MatrixRepresentation G ι) (i j : ι) (g : G) :
    ρ.entry i j g = (ρ.toRepresentation g (Pi.single j 1)) i := by
  simp [entry, toRepresentation, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct,
    Pi.single_apply]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Coordinate realization of any continuous finite-dimensional representation.
Orbit continuity is stated explicitly: mathlib's `ContRepresentation` alone only
requires each action operator to be continuous in the vector variable. -/
def ofRepresentation (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V)
    (hρ : ∀ v, Continuous fun g => ρ g v) : MatrixRepresentation G ι where
  toMonoidHom := (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ
  continuous_entry i j := by
    change Continuous fun g => (LinearMap.toMatrixAlgEquiv b) (ρ g) i j
    simp only [LinearMap.toMatrixAlgEquiv_apply]
    let := b.finiteDimensional_of_finite
    exact ((b.coord i).continuous_of_finiteDimensional).comp (hρ (b j))

theorem coefficient_ofRepresentation (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V)
    (hρ : ∀ v, Continuous fun g => ρ g v) (l : V →ₗ[ℂ] ℂ) (v : V) (g : G) :
    (ofRepresentation b ρ hρ).coefficient (fun i => l (b i)) (b.repr v) g = l (ρ g v) := by
  rw [coefficient_apply]
  change (∑ i, ∑ j, l (b i) * (LinearMap.toMatrixAlgEquiv b) (ρ g) i j * b.repr v j) = _
  simp only [LinearMap.toMatrixAlgEquiv_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_mul]
  have h : (∑ i, l (b i) * b.repr (ρ g (b j)) i) = l (ρ g (b j)) := by
    conv_rhs => rw [← b.sum_repr (ρ g (b j))]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, mul_comm]
  rw [h]
  simp [mul_comm]

end MatrixRepresentation

/-- Coordinate coefficients of all finite-dimensional continuous representations.
The fixed finite index types keep this set independent of a representation's universe. -/
def coefficientGenerators : Set C(G, ℂ) :=
  {f | ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (i j : Fin n), f = ρ.entry i j}

/-- Finite linear combinations of matrix coefficients; no topological closure is taken. -/
def representativeSubmodule : Submodule ℂ C(G, ℂ) :=
  Submodule.span ℂ (coefficientGenerators G)

variable {G}

theorem entry_mem_representative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : MatrixRepresentation G ι) (i j : ι) : ρ.entry i j ∈ representativeSubmodule G := by
  apply Submodule.subset_span
  refine ⟨Fintype.card ι, ρ.reindex (Fintype.equivFin ι),
    Fintype.equivFin ι i, Fintype.equivFin ι j, ?_⟩
  simp

theorem representative_one : (1 : C(G, ℂ)) ∈ representativeSubmodule G := by
  let ρ : MatrixRepresentation G (Fin 1) := ⟨1, fun _ _ => continuous_const⟩
  convert entry_mem_representative ρ 0 0 using 1
  ext g
  simp [ρ, MatrixRepresentation.entry]

theorem representative_mul {f h : C(G, ℂ)} (hf : f ∈ representativeSubmodule G)
    (hh : h ∈ representativeSubmodule G) : f * h ∈ representativeSubmodule G := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, ρ, i, j, rfl⟩ := hf
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨m, σ, k, l, rfl⟩ := hh
      exact entry_mem_representative (ρ.tensor σ) (i, k) (j, l)
    | zero => simp
    | add x y hx hy hx' hy' =>
      simpa [mul_add] using (representativeSubmodule G).add_mem hx' hy'
    | smul a x hx hx' =>
      simpa [mul_smul_comm] using (representativeSubmodule G).smul_mem a hx'
  | zero => simp
  | add x y hx hy hx' hy' =>
    simpa [add_mul] using (representativeSubmodule G).add_mem hx' hy'
  | smul a x hx hx' =>
    simpa [smul_mul_assoc] using (representativeSubmodule G).smul_mem a hx'

theorem representative_star {f : C(G, ℂ)} (hf : f ∈ representativeSubmodule G) :
    star f ∈ representativeSubmodule G := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, ρ, i, j, rfl⟩ := hf
    exact entry_mem_representative ρ.conjugate i j
  | zero => simp
  | add x y hx hy hx' hy' =>
    simpa using (representativeSubmodule G).add_mem hx' hy'
  | smul a x hx hx' =>
    simpa [star_smul] using (representativeSubmodule G).smul_mem (star a) hx'

/-- The manuscript's unital algebra of representative functions. -/
def representativeFunctions : Subalgebra ℂ C(G, ℂ) where
  __ := representativeSubmodule G
  one_mem' := representative_one
  mul_mem' := representative_mul
  algebraMap_mem' a := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      (representativeSubmodule G).smul_mem a representative_one

/-- Complex conjugation closes the representative algebra. -/
def representativeStarAlgebra : StarSubalgebra ℂ C(G, ℂ) where
  __ := representativeFunctions (G := G)
  star_mem' := representative_star

theorem coefficient_mem_representative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : MatrixRepresentation G ι) (a v : ι → ℂ) :
    ρ.coefficient a v ∈ representativeFunctions (G := G) := by
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact (representativeSubmodule G).smul_mem _ (entry_mem_representative ρ i j)

/-- Every coefficient of an arbitrary finite-dimensional continuous representation
belongs to the coordinate-defined algebra, in any universe. -/
theorem representation_coefficient_mem {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : ∀ v, Continuous fun g => ρ g v) (l : V →ₗ[ℂ] ℂ) (v : V) :
    (⟨fun g => l (ρ g v), l.continuous_of_finiteDimensional.comp (hρ v)⟩ : C(G, ℂ)) ∈
      representativeFunctions (G := G) := by
  let b := Module.finBasis ℂ V
  convert coefficient_mem_representative (MatrixRepresentation.ofRepresentation b ρ hρ)
    (fun i => l (b i)) (b.repr v) using 1
  ext g
  exact (MatrixRepresentation.coefficient_ofRepresentation b ρ hρ l v g).symm

/-- Usual coefficients on finite coordinate spaces, defined using linear representations
and explicitly continuous orbit maps. `representation_coefficient_mem` handles arbitrary
finite-dimensional spaces by choosing a basis. -/
def continuousRepresentationCoefficients (G : Type*) [Monoid G] [TopologicalSpace G] :
    Set C(G, ℂ) :=
  {f | ∃ (n : ℕ) (ρ : Representation ℂ G (Fin n → ℂ)),
    (∀ v, Continuous fun g => ρ g v) ∧
      ∃ (l : (Fin n → ℂ) →ₗ[ℂ] ℂ) (v : Fin n → ℂ), ∀ g, f g = l (ρ g v)}

/-- Exact finite-span correspondence with the usual definition of representative functions. -/
theorem representative_eq_span_coefficients : representativeSubmodule G =
    Submodule.span ℂ (continuousRepresentationCoefficients G) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨n, ρ, i, j, rfl⟩
    apply Submodule.subset_span
    exact ⟨n, ρ.toRepresentation, ρ.continuous_orbit, LinearMap.proj i,
      Pi.single j 1, ρ.entry_as_coefficient i j⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨n, ρ, hρ, l, v, hf⟩
    have heq : f = (⟨fun g => l (ρ g v),
        l.continuous_of_finiteDimensional.comp (hρ v)⟩ : C(G, ℂ)) :=
      ContinuousMap.ext hf
    rw [heq]
    exact representation_coefficient_mem ρ hρ l v

/-- Lemma `lem:representative-algebra` (algebra assertion): the finite span in the
usual coefficient definition is exactly the constructed unital star algebra.
The tensor, conjugate, and pullback assertions are `coefficient_mul`,
`coefficient_conj`, and `representative_comp`. -/
theorem representative_algebra :
    (representativeStarAlgebra (G := G)).toSubalgebra.toSubmodule =
      Submodule.span ℂ (continuousRepresentationCoefficients G) :=
  representative_eq_span_coefficients

variable {H : Type*} [Monoid H] [TopologicalSpace H]

theorem representative_comp {f : C(H, ℂ)} (hf : f ∈ representativeFunctions (G := H))
    (π : G →* H) (hπ : Continuous π) :
    f.comp ⟨π, hπ⟩ ∈ representativeFunctions (G := G) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, ρ, i, j, rfl⟩ := hf
    exact entry_mem_representative (ρ.pullback π hπ) i j
  | zero => exact (representativeSubmodule G).zero_mem
  | add x y hx hy hx' hy' => exact (representativeSubmodule G).add_mem hx' hy'
  | smul a x hx hx' => exact (representativeSubmodule G).smul_mem a hx'

/-- Pullback is an algebra homomorphism on the actual representative algebras. -/
def representativePullback (π : G →* H) (hπ : Continuous π) :
    representativeFunctions (G := H) →ₐ[ℂ] representativeFunctions (G := G) :=
  ((ContinuousMap.compRightAlgHom ℂ ℂ ⟨π, hπ⟩).comp
    (representativeFunctions (G := H)).val).codRestrict _
      (fun f => representative_comp f.property π hπ)

end XZMathieuSU2Counterexamples

/- Adapted from MathieuProperty/RepresentativeFunctions.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
