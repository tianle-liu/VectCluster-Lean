/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalDegreeTerms
import Verification.FiniteBiproductWordEntries

/-!
# Path Word Object Transport

Exact object transports between actual binary word summands and the literal normalized path words, including all homogeneous degree casts.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathWordObjectTransport
open Classical CategoryTheory CategoryTheory.Limits
variable {A : Type*} [Category A] [Abelian A]
attribute [local instance] Abelian.hasFiniteBiproducts
variable (Z : A) (M : ℤ → A)
section Y
variable (a p : ℕ)
local notation "Indices" => Σ I : {I : PathCochains.Config (2*a) // I.val.card=p},
  BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property))

theorem y_degree (x : Indices) :
    (PathWeightFiltration.weight (PathStrictTermIndices.yWords a p x).val:ℤ)=
    StrictTorusSymbolInput.degree (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates x.1.val.property)) x.2 := by
  have hh := PathStrictTermIndices.y_weight x.1.val x.2
  simpa only [x.1.property] using hh

def yObject (x : Indices) :
    PathOriginalDegreeTerms.wordObject Z M (PathStrictTermIndices.yWords a p x).val ≅
    StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates x.1.val.property)) x.2 :=
  eqToIso (by
    unfold PathOriginalDegreeTerms.wordObject StrictTorusSymbolInput.summand
    rw [←y_degree a p x]
    simp only [Nat.cast_eq_zero])

theorem y_wordsIso : PathOriginalDegreeTerms.yWordsIso Z M a p=
    FiniteBiproductWordEntries.wordIso
      (fun I : {I : PathCochains.Config (2*a) // I.val.card=p}=>
        BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
      (fun I=>StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
      (fun x=>PathOriginalDegreeTerms.wordObject Z M x.val) (PathStrictTermIndices.yWords a p)
      (yObject Z M a p) := rfl

omit [Abelian A] in
theorem y_positive (x : Indices)
    (hw : PathWeightFiltration.weight (PathStrictTermIndices.yWords a p x).val≠0)
    (hd : StrictTorusSymbolInput.degree (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates x.1.val.property)) x.2≠0) :
    eqToHom (if_neg hw).symm ≫ (yObject Z M a p x).hom ≫ eqToHom (if_neg hd)=
      eqToHom (congrArg M (y_degree a p x)) := by
  simp only [yObject,eqToIso.hom,eqToHom_trans]

omit [Abelian A] in
theorem y_positive_inv (x : Indices)
    (hw : PathWeightFiltration.weight (PathStrictTermIndices.yWords a p x).val≠0)
    (hd : StrictTorusSymbolInput.degree (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates x.1.val.property)) x.2≠0) :
    eqToHom (if_neg hd).symm ≫ (yObject Z M a p x).inv ≫ eqToHom (if_neg hw)=
      eqToHom (congrArg M (y_degree a p x).symm) := by
  simp only [yObject,eqToIso.inv,eqToHom_trans]

#print axioms y_degree
#print axioms yObject
#print axioms y_wordsIso
#print axioms y_positive
#print axioms y_positive_inv
end Y
section Z
variable (n p : ℕ)
local notation "Indices" => Σ I : {I : PathCochains.Config (n) // I.val.card=p},
  BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property))

theorem z_degree (x : Indices) :
    (PathWeightFiltration.weight (PathStrictTermIndices.zWords n p x).val:ℤ)=
    StrictTorusSymbolInput.degree (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates x.1.val.property)) x.2 := by
  have hh := PathStrictTermIndices.z_weight x.1.val x.2
  simpa only [x.1.property] using hh

def zObject (x : Indices) :
    PathOriginalDegreeTerms.wordObject Z M (PathStrictTermIndices.zWords n p x).val ≅
    StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates x.1.val.property)) x.2 :=
  eqToIso (by
    unfold PathOriginalDegreeTerms.wordObject StrictTorusSymbolInput.summand
    rw [←z_degree n p x]
    simp only [Nat.cast_eq_zero])

theorem z_wordsIso : PathOriginalDegreeTerms.zWordsIso Z M n p=
    FiniteBiproductWordEntries.wordIso
      (fun I : {I : PathCochains.Config (n) // I.val.card=p}=>
        BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
      (fun I=>StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
      (fun x=>PathOriginalDegreeTerms.wordObject Z M x.val) (PathStrictTermIndices.zWords n p)
      (zObject Z M n p) := rfl

omit [Abelian A] in
theorem z_positive (x : Indices)
    (hw : PathWeightFiltration.weight (PathStrictTermIndices.zWords n p x).val≠0)
    (hd : StrictTorusSymbolInput.degree (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates x.1.val.property)) x.2≠0) :
    eqToHom (if_neg hw).symm ≫ (zObject Z M n p x).hom ≫ eqToHom (if_neg hd)=
      eqToHom (congrArg M (z_degree n p x)) := by
  simp only [zObject,eqToIso.hom,eqToHom_trans]

omit [Abelian A] in
theorem z_positive_inv (x : Indices)
    (hw : PathWeightFiltration.weight (PathStrictTermIndices.zWords n p x).val≠0)
    (hd : StrictTorusSymbolInput.degree (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates x.1.val.property)) x.2≠0) :
    eqToHom (if_neg hd).symm ≫ (zObject Z M n p x).inv ≫ eqToHom (if_neg hw)=
      eqToHom (congrArg M (z_degree n p x).symm) := by
  simp only [zObject,eqToIso.inv,eqToHom_trans]

#print axioms z_degree
#print axioms zObject
#print axioms z_wordsIso
#print axioms z_positive
#print axioms z_positive_inv
end Z

end Verification.PathWordObjectTransport
