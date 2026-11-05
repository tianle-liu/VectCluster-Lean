/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestQuotient
import Verification.FrozenQuotientCoordinates

/-!
# Path Forest Frozen Basis

The manuscript's frozen basis and C_1=C_std+UB for an actual linear
path forest. AS supplies full integral generation internally; the odd
quotient, frozen basis, rank bound, and correction matrix are constructed.
-/

noncomputable section
namespace Verification.PathForestFrozenBasis
open Classical Verification.PathForestMatching Verification.PathForestFullRank
  Verification.PathForestComponentMatrix Verification.PathForestQuotient
variable {S F : Type} [Fintype S] [Fintype F] (m : S → ℕ) (o : S → Bool)
variable (C : Matrix F (PIndex m o) ℤ) (G : Matrix F (QIndex m) ℤ)

def frozenMatrix : Matrix F (Vertices m o) ℤ := fun f=>Sum.elim (C f) (G f)

theorem full_row_action (x : Vertices m o → ℤ) (y : F → ℤ) :
    (extended m o (fun _ _=>1) (fun _ _=>1) C G).transpose.mulVec (Sum.elim x y)=
      (ordinaryMatrix m o).transpose.mulVec x+(frozenMatrix m o C G).transpose.mulVec y := by
  have he (r i : Vertices m o) : extended m o (fun _ _=>1) (fun _ _=>1) C G (Sum.inl r) i=
      ordinaryMatrix m o r i := by cases r <;> cases i <;> rfl
  have hf (f : F) (i : Vertices m o) : extended m o (fun _ _=>1) (fun _ _=>1) C G (Sum.inr f) i=
      frozenMatrix m o C G f i := by cases i <;> rfl
  funext i
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,Pi.add_apply,he,hf]

variable (hAS : AnticliqueSubcolumns.AS (extended m o (fun _ _=>1) (fun _ _=>1) C G)
  (BipartiteASCoordinates.selected (PIndex m o) (QIndex m)))

include hAS in
theorem full_rows : Function.Surjective
    ((ordinaryMatrix m o).transpose.mulVecLin.coprod (frozenMatrix m o C G).transpose.mulVecLin) := by
  intro x
  obtain ⟨y,hy⟩:=PathForestFullRank.rows_surjective m o (fun _ _=>1) (fun _ _=>1) C G hAS x
  refine ⟨(fun i=>y (Sum.inl i),fun f=>y (Sum.inr f)),?_⟩
  change (ordinaryMatrix m o).transpose.mulVec (fun i=>y (Sum.inl i))+
    (frozenMatrix m o C G).transpose.mulVec (fun f=>y (Sum.inr f))=x
  rw [← full_row_action]
  have he : Sum.elim (fun i=>y (Sum.inl i)) (fun f=>y (Sum.inr f))=y := by funext i;cases i <;> rfl
  rw [he]
  exact hy

def coordinates : (F → ℤ) ≃ₗ[ℤ] ((Odd o → ℤ) × (Fin (Fintype.card F-Fintype.card (Odd o)) → ℤ)) :=
  FrozenQuotientCoordinates.coordinates (ordinaryMatrix m o).transpose.mulVecLin
    (frozenMatrix m o C G).transpose.mulVecLin (quotientMap m o)
      (quotient_surjective m o) (quotient_rows_zero m o) (full_rows m o C G hAS)

def basis : Basis (Odd o ⊕ Fin (Fintype.card F-Fintype.card (Odd o))) ℤ (F → ℤ) :=
  FrozenQuotientCoordinates.basis (ordinaryMatrix m o).transpose.mulVecLin
    (frozenMatrix m o C G).transpose.mulVecLin (quotientMap m o)
      (quotient_surjective m o) (quotient_rows_zero m o) (full_rows m o C G hAS)

include hAS in
theorem enough_frozen : Fintype.card (Odd o)≤Fintype.card F :=
  FrozenQuotientCoordinates.enough_frozen (ordinaryMatrix m o).transpose.mulVecLin
    (frozenMatrix m o C G).transpose.mulVecLin (quotientMap m o)
      (quotient_surjective m o) (quotient_rows_zero m o) (full_rows m o C G hAS)

abbrev NewFrozen := Odd o ⊕ Fin (Fintype.card F-Fintype.card (Odd o))
def changedFrozen : Matrix (NewFrozen (F:=F) o) (Vertices m o) ℤ :=
  fun a=>(frozenMatrix m o C G).transpose.mulVec (basis m o C G hAS a)
def standardFrozen : Matrix (NewFrozen (F:=F) o) (Vertices m o) ℤ :=
  FrozenQuotientCoordinates.standardRow (F:=F) (endpoint m o)

def correction : Matrix (NewFrozen (F:=F) o) (Vertices m o) ℤ := fun a=>
  FrozenQuotientCoordinates.mutableCorrection (ordinaryMatrix m o).transpose.mulVecLin
    (frozenMatrix m o C G).transpose.mulVecLin (quotientMap m o)
      (quotient_surjective m o) (quotient_rows_zero m o) (full_rows m o C G hAS)
        (rows_eq_kernel m o) (endpoint m o) (endpoint_right m o) a

theorem frozen_normalform : changedFrozen m o C G hAS=standardFrozen (F:=F) m o+
    correction m o C G hAS*ordinaryMatrix m o := by
  ext a i
  have h:=FrozenQuotientCoordinates.corrected_row (ordinaryMatrix m o).transpose.mulVecLin
    (frozenMatrix m o C G).transpose.mulVecLin (quotientMap m o)
      (quotient_surjective m o) (quotient_rows_zero m o) (full_rows m o C G hAS)
        (rows_eq_kernel m o) (endpoint m o) (endpoint_right m o) a
  have hi:=congrFun h i
  simpa only [changedFrozen,standardFrozen,correction,basis,FrozenQuotientCoordinates.standardRow,
    Matrix.mulVecLin_apply,Pi.add_apply,Matrix.add_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct,
    Matrix.transpose_apply,mul_comm] using hi

theorem standard_unused (k : Fin (Fintype.card F-Fintype.card (Odd o))) :
    standardFrozen (F:=F) m o (Sum.inr k)=0 := by
  change endpoint m o 0=0
  exact map_zero _

#print axioms frozenMatrix
#print axioms full_row_action
#print axioms full_rows
#print axioms coordinates
#print axioms basis
#print axioms enough_frozen
#print axioms NewFrozen
#print axioms changedFrozen
#print axioms standardFrozen
#print axioms correction
#print axioms frozen_normalform
#print axioms standard_unused
end Verification.PathForestFrozenBasis
