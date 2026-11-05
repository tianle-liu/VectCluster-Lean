/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BooleanCubeCoordinates
import Verification.SignatureLattice
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Binary Pfister Basis

The integral change from binary characters to products of character
minus one is unimodular. This is an algebraic group-ring basis, with no
identification through a real signature lattice.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.BinaryPfisterBasis
variable (α : Type*) [Fintype α]

abbrev Group := Multiplicative (α → ZMod 2)
abbrev Ring := MonoidAlgebra ℤ (Group α)

def matrix : Matrix (Finset α) (Finset α) ℤ :=
  fun B A => if B ⊆ A then (-1)^(A.card-B.card) else 0

omit [Fintype α] in
theorem triangular : (matrix α).BlockTriangular Finset.card := by
  intro A B h
  exact if_neg (fun hAB => (Nat.not_le_of_lt h) (Finset.card_le_card hAB))

omit [Fintype α] in
theorem diagonal (k : ℕ) : (matrix α).toSquareBlock Finset.card k = 1 := by
  ext A B
  simp only [Matrix.toSquareBlock_def,matrix,Matrix.one_apply]
  by_cases h : A = B
  · subst B
    simp
  · have hh : ¬ A.val ⊆ B.val := by
      intro hs
      apply h
      exact Subtype.ext (Finset.eq_of_subset_of_card_le hs (by omega))
    simp [h,hh]

theorem determinant : (matrix α).det = 1 := by
  rw [(triangular α).det]
  simp [diagonal]

def transform : (Finset α → ℤ) ≃ₗ[ℤ] (Finset α → ℤ) :=
  LinearEquiv.ofBijective (matrix α).mulVecLin (by
    have hu : IsUnit (matrix α) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [determinant]; exact isUnit_one)
    exact ⟨Matrix.mulVec_injective_of_isUnit hu,Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

def indexEquiv : Finset α ≃ Group α :=
  BooleanCubeCoordinates.cubeEquiv.trans Multiplicative.ofAdd

def characterEquiv : (Finset α → ℤ) ≃ₗ[ℤ] Ring α :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (Finset α)).symm.trans
    (Finsupp.domLCongr (indexEquiv α))

def equiv : (Finset α → ℤ) ≃ₗ[ℤ] Ring α :=
  (transform α).trans (characterEquiv α)

def basis : Basis (Finset α) ℤ (Ring α) :=
  (Pi.basisFun ℤ (Finset α)).map (equiv α)

theorem transform_single (A B : Finset α) :
    transform α (Pi.single A 1) B = matrix α B A := by
  change (matrix α).mulVec (Pi.single A 1) B = _
  simp [Matrix.mulVec,dotProduct,Pi.single_apply]

theorem character_single (A : Finset α) :
    characterEquiv α (Pi.single A 1) = MonoidAlgebra.of ℤ _ (indexEquiv α A) := by
  change Finsupp.domLCongr (R := ℤ) (indexEquiv α)
    ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Finset α)).symm (Pi.single A 1)) = _
  have he : (Finsupp.linearEquivFunOnFinite ℤ ℤ (Finset α)).symm (Pi.single A 1) = Finsupp.single A 1 := by
    ext B
    simp [Pi.single_apply,Finsupp.single_apply]
  rw [he]
  simp [MonoidAlgebra.of_apply]

#print axioms Group
#print axioms Ring
#print axioms matrix
#print axioms triangular
#print axioms diagonal
#print axioms determinant
#print axioms transform
#print axioms indexEquiv
#print axioms characterEquiv
#print axioms equiv
#print axioms basis
#print axioms transform_single
#print axioms character_single
end Verification.BinaryPfisterBasis
