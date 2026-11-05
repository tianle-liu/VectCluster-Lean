/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestMatching
import Verification.BipartiteMatrixRetraction

/-!
# Path Forest Full Rank

Actual full extended integer matrices of finite signed path forests.
The component matching retraction and the literal AS selected-column map
construct the full left inverse. Frozen columns are completely arbitrary.
-/

noncomputable section
namespace Verification.PathForestFullRank
open Classical Verification.PathForestMatching
variable {S F : Type} [Fintype S] [Fintype F]
variable (m : S → ℕ) (o : S → Bool)
abbrev PIndex := Σ s,largeIndex (m s) (o s)
abbrev QIndex := Σ s,Fin (m s)

def pCoordinates : (PIndex m o → ℤ) ≃ₗ[ℤ] Large m o :=
  LinearEquiv.piCurry ℤ (fun s (_ : largeIndex (m s) (o s))=>ℤ)
def qCoordinates : (QIndex m → ℤ) ≃ₗ[ℤ] Small m :=
  LinearEquiv.piCurry ℤ (fun s (_ : Fin (m s))=>ℤ)

variable (u : (s : S) → largeIndex (m s) (o s) → ℤˣ) (v : (s : S) → Fin (m s) → ℤˣ)
def matchingMap : (QIndex m → ℤ) →ₗ[ℤ] (PIndex m o → ℤ) :=
  (pCoordinates m o).symm.toLinearMap.comp
    ((signedMatching m o u v).comp (qCoordinates m).toLinearMap)
def matchingRetraction : (PIndex m o → ℤ) →ₗ[ℤ] (QIndex m → ℤ) :=
  (qCoordinates m).symm.toLinearMap.comp
    ((signedRetraction m o u v).comp (pCoordinates m o).toLinearMap)

omit [Fintype S] in
theorem matching_left : (matchingRetraction m o u v).comp (matchingMap m o u v)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (qCoordinates m).symm (signedRetraction m o u v
    (pCoordinates m o ((pCoordinates m o).symm (signedMatching m o u v (qCoordinates m x)))))=x
  rw [LinearEquiv.apply_symm_apply]
  have h:=LinearMap.congr_fun (signed_left m o u v) (qCoordinates m x)
  change signedRetraction m o u v (signedMatching m o u v (qCoordinates m x))=qCoordinates m x at h
  rw [h,LinearEquiv.symm_apply_apply]

def matchingMatrix : Matrix (PIndex m o) (QIndex m) ℤ := LinearMap.toMatrix' (matchingMap m o u v)

theorem matchingMatrix_map : (matchingMatrix m o u v).mulVecLin=matchingMap m o u v := by
  exact Matrix.toLin'_toMatrix' _

def principal : Matrix (PIndex m o ⊕ QIndex m) (PIndex m o ⊕ QIndex m) ℤ :=
  Matrix.fromBlocks 0 (matchingMatrix m o u v) (-(matchingMatrix m o u v).transpose) 0

variable (C : Matrix F (PIndex m o) ℤ) (G : Matrix F (QIndex m) ℤ)
def extended : Matrix ((PIndex m o ⊕ QIndex m) ⊕ F) (PIndex m o ⊕ QIndex m) ℤ :=
  BipartiteASCoordinates.matrix (matchingMatrix m o u v) (-(matchingMatrix m o u v).transpose) C G

variable (hAS : AnticliqueSubcolumns.AS (extended m o u v C G)
  (BipartiteASCoordinates.selected (PIndex m o) (QIndex m)))

def retraction : (((PIndex m o ⊕ QIndex m) ⊕ F) → ℤ) →ₗ[ℤ] ((PIndex m o ⊕ QIndex m) → ℤ) :=
  BipartiteMatrixRetraction.retraction (matchingMatrix m o u v) (-(matchingMatrix m o u v).transpose)
    C G (matchingRetraction m o u v) hAS

theorem left : (retraction m o u v C G hAS).comp (extended m o u v C G).mulVecLin=LinearMap.id := by
  apply BipartiteMatrixRetraction.left
  rw [matchingMatrix_map]
  exact matching_left m o u v

include hAS in
theorem full_rank_saturated : Function.Injective (extended m o u v C G).mulVecLin ∧
    FreezingLattice.Saturated (LinearMap.range (extended m o u v C G).mulVecLin) := by
  apply BipartiteMatrixRetraction.full_rank_saturated _ _ C G (matchingRetraction m o u v) _ hAS
  rw [matchingMatrix_map]
  exact matching_left m o u v

include hAS in
theorem rows_surjective : Function.Surjective (extended m o u v C G).transpose.mulVecLin := by
  apply BipartiteMatrixRetraction.rows_surjective _ _ C G (matchingRetraction m o u v) _ hAS
  rw [matchingMatrix_map]
  exact matching_left m o u v

#print axioms PIndex
#print axioms QIndex
#print axioms pCoordinates
#print axioms qCoordinates
#print axioms matchingMap
#print axioms matchingRetraction
#print axioms matching_left
#print axioms matchingMatrix
#print axioms matchingMatrix_map
#print axioms principal
#print axioms extended
#print axioms retraction
#print axioms left
#print axioms full_rank_saturated
#print axioms rows_surjective

end Verification.PathForestFullRank
