/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BipartiteASCoordinates

/-!
# Bipartite Matrix Retraction

The original extended integer matrix has a constructed left inverse,
using AS on the independent bipartition and the proved unit matching. Its
transpose is therefore integrally surjective, as needed for frozen rows.
-/

noncomputable section
namespace Verification.BipartiteMatrixRetraction
open Classical Verification.BipartiteASCoordinates Verification.PathLattice
variable {P Q F : Type} [Fintype P] [Fintype Q] [Fintype F]
variable (D : Matrix P Q ℤ) (E : Matrix Q P ℤ) (C : Matrix F P ℤ) (G : Matrix F Q ℤ)

def allCoordinates : (((P ⊕ Q) ⊕ F) → ℤ) ≃ₗ[ℤ] ((P → ℤ) × ((Q → ℤ) × (F → ℤ))) where
  toFun x := (fun p=>x (Sum.inl (Sum.inl p)),(fun q=>x (Sum.inl (Sum.inr q)),fun f=>x (Sum.inr f)))
  invFun x := Sum.elim (Sum.elim x.1 x.2.1) x.2.2
  left_inv x := by funext i;rcases i with (p|q)|f <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def mutableCoordinates : ((P ⊕ Q) → ℤ) ≃ₗ[ℤ] ((P → ℤ) × (Q → ℤ)) :=
  LinearEquiv.sumArrowLequivProdArrow P Q ℤ ℤ

omit [Fintype F] in
theorem matrix_action (x : (P ⊕ Q) → ℤ) :
    allCoordinates ((matrix D E C G).mulVec x)=
      bipartiteExtension D.mulVecLin E.mulVecLin C.mulVecLin G.mulVecLin (mutableCoordinates x) := by
  apply Prod.ext
  · funext p
    simp [allCoordinates,mutableCoordinates,bipartiteExtension,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,matrix]
  · apply Prod.ext
    · funext q
      simp [allCoordinates,mutableCoordinates,bipartiteExtension,Matrix.mulVec,dotProduct,
        Fintype.sum_sum_type,matrix]
    · funext f
      simp [allCoordinates,mutableCoordinates,bipartiteExtension,Matrix.mulVec,dotProduct,
        Fintype.sum_sum_type,matrix]

variable (J : (P → ℤ) →ₗ[ℤ] (Q → ℤ)) (hJ : J.comp D.mulVecLin=LinearMap.id)
variable (hAS : AnticliqueSubcolumns.AS (matrix D E C G) (selected P Q))

def retraction : (((P ⊕ Q) ⊕ F) → ℤ) →ₗ[ℤ] ((P ⊕ Q) → ℤ) :=
  mutableCoordinates.symm.toLinearMap.comp
    ((extensionRetraction J (selectedRetraction D E C G hAS) G.mulVecLin).comp allCoordinates.toLinearMap)

include hJ in
theorem left : (retraction D E C G J hAS).comp (matrix D E C G).mulVecLin=LinearMap.id := by
  apply LinearMap.ext
  intro x
  change mutableCoordinates.symm (extensionRetraction J (selectedRetraction D E C G hAS)
    G.mulVecLin (allCoordinates ((matrix D E C G).mulVec x)))=x
  rw [matrix_action]
  have h:=LinearMap.congr_fun (bipartiteExtension_split D.mulVecLin E.mulVecLin C.mulVecLin
    G.mulVecLin J (selectedRetraction D E C G hAS) hJ (selectedRetraction_left D E C G hAS))
      (mutableCoordinates x)
  change extensionRetraction J (selectedRetraction D E C G hAS) G.mulVecLin
    (bipartiteExtension D.mulVecLin E.mulVecLin C.mulVecLin G.mulVecLin (mutableCoordinates x))=
      mutableCoordinates x at h
  rw [h,LinearEquiv.symm_apply_apply]

include hJ hAS in
theorem full_rank_saturated : Function.Injective (matrix D E C G).mulVecLin ∧
    FreezingLattice.Saturated (LinearMap.range (matrix D E C G).mulVecLin) := by
  have hr : Function.LeftInverse (retraction D E C G J hAS) (matrix D E C G).mulVecLin :=
    fun x=>LinearMap.congr_fun (left D E C G J hJ hAS) x
  exact ⟨hr.injective,CliqueSaturation.split_range_saturated _ _ hr⟩

def retractionMatrix : Matrix (P ⊕ Q) ((P ⊕ Q) ⊕ F) ℤ :=
  LinearMap.toMatrix' (retraction D E C G J hAS)

include hJ in
theorem matrix_left : retractionMatrix D E C G J hAS * matrix D E C G=1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,retractionMatrix,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
  exact left D E C G J hJ hAS

include hJ hAS in
theorem rows_surjective : Function.Surjective (matrix D E C G).transpose.mulVecLin := by
  intro x
  refine ⟨(retractionMatrix D E C G J hAS).transpose.mulVec x,?_⟩
  change (matrix D E C G).transpose.mulVec ((retractionMatrix D E C G J hAS).transpose.mulVec x)=x
  rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,matrix_left D E C G J hJ hAS,Matrix.transpose_one,Matrix.one_mulVec]

#print axioms allCoordinates
#print axioms mutableCoordinates
#print axioms matrix_action
#print axioms retraction
#print axioms left
#print axioms full_rank_saturated
#print axioms retractionMatrix
#print axioms matrix_left
#print axioms rows_surjective

end Verification.BipartiteMatrixRetraction
