/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalConfigurationIndex
import Verification.PathActualColumnDegrees
import Verification.ActualCellThom
import Verification.PathWeightFiltration

/-!
# Path Strict Term Indices

Exact degreewise indices for the actual path strata and their torus
word summands. Both cellular degree and MW weight are preserved.
-/
noncomputable section
open scoped Classical
namespace Verification.PathStrictTermIndices
open Verification.PathCochains Verification.PathCompression
open Verification.PathNormalizedBasis Verification.PathEndpointWords
open Verification.PathActualWordIndices Verification.PathWeightFiltration
open Verification.PathOriginalConfigurationIndex

def configDegree {κ : Type} {n : ℕ} (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
    (hB : ∀ a i : Fin n,B (Sum.inl a) (Sum.inl i)=PathLattice.pathMatrix n a i) (p : ℕ) :
    {I : Config n // I.val.card=p} ≃ ActualCellThom.Index κ n B p where
  toFun I := ⟨(configEquiv B hB I.val).val,(config_card B hB I.val).trans I.property,
    (configEquiv B hB I.val).property⟩
  invFun J := ⟨(configEquiv B hB).symm ⟨J.val,J.property.2⟩,by
    have he := config_card B hB ((configEquiv B hB).symm ⟨J.val,J.property.2⟩)
    rw [Equiv.apply_symm_apply] at he
    exact he.symm.trans J.property.1⟩
  left_inv I := by apply Subtype.ext; exact (configEquiv B hB).symm_apply_apply I.val
  right_inv J := by
    apply Subtype.ext
    change ((configEquiv B hB) ((configEquiv B hB).symm ⟨J.val,J.property.2⟩)).val=J.val
    rw [Equiv.apply_symm_apply]

def zWords (n p : ℕ) :
    (Σ I : {I : Config n // I.val.card=p},
      BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property))) ≃
    {x : NormalIndex RightNormal n // -(PathStratumGrading.degree x)= -(p:ℤ)} where
  toFun x := ⟨⟨x.1.val,zWordEquiv x.1.val.property x.2⟩,by
    change -(x.1.val.val.card:ℤ)= -(p:ℤ)
    rw [x.1.property]⟩
  invFun x := ⟨⟨x.val.1,by
    have hx := x.property
    change -(x.val.1.val.card:ℤ)= -(p:ℤ) at hx
    omega⟩,(zWordEquiv x.val.1.property).symm x.val.2⟩
  left_inv x := by
    cases x with
    | mk I w =>
      cases I with
      | mk I hI =>
        dsimp only
        simp only [Equiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    change (⟨x.val.1,zWordEquiv x.val.1.property ((zWordEquiv x.val.1.property).symm x.val.2)⟩ : NormalIndex RightNormal n)=_
    rw [Equiv.apply_symm_apply]

def yWords (a p : ℕ) :
    (Σ I : {I : Config (2*a) // I.val.card=p},
      BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property))) ≃
    {x : NormalIndex BothNormal (2*a) // -(PathStratumGrading.degree x)= -(p:ℤ)} where
  toFun x := ⟨⟨x.1.val,yWordEquiv x.1.val.property x.2⟩,by
    change -(x.1.val.val.card:ℤ)= -(p:ℤ)
    rw [x.1.property]⟩
  invFun x := ⟨⟨x.val.1,by
    have hx := x.property
    change -(x.val.1.val.card:ℤ)= -(p:ℤ) at hx
    omega⟩,(yWordEquiv x.val.1.property).symm x.val.2⟩
  left_inv x := by
    cases x with
    | mk I w =>
      cases I with
      | mk I hI =>
        dsimp only
        simp only [Equiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    change (⟨x.val.1,yWordEquiv x.val.1.property ((yWordEquiv x.val.1.property).symm x.val.2)⟩ : NormalIndex BothNormal (2*a))=_
    rw [Equiv.apply_symm_apply]

theorem z_weight {n : ℕ} (I : Config n)
    (i : BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.property))) :
    (weight (zIndexEquiv n ⟨I,i⟩):ℤ)=
      StrictTorusSymbolInput.degree (Fintype.card (Fin I.val.card))
        (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.property)) i := by
  change ((I.val.card+(zWordEquiv I.property i).val.count true:ℕ):ℤ)=_
  rw [Nat.cast_add,PathActualColumnDegrees.z_count]
  simp only [StrictTorusSymbolInput.degree,Fintype.card_fin]

theorem y_weight {a : ℕ} (I : Config (2*a))
    (i : BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.property))) :
    (weight (yIndexEquiv a ⟨I,i⟩):ℤ)=
      StrictTorusSymbolInput.degree (Fintype.card (Fin I.val.card))
        (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.property)) i := by
  change ((I.val.card+(yWordEquiv I.property i).val.count true:ℕ):ℤ)=_
  rw [Nat.cast_add,PathActualColumnDegrees.y_count]
  simp only [StrictTorusSymbolInput.degree,Fintype.card_fin]

#print axioms configDegree
#print axioms zWords
#print axioms yWords
#print axioms z_weight
#print axioms y_weight
end Verification.PathStrictTermIndices
