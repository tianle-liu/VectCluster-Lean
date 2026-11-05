/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathStrictTermIndices
import Verification.PathOriginalStrictCells
import Verification.OriginalStrictProjectionDetection

/-!
# Path Original Degree Terms

The actual finite sum of path-stratum terms is the full normal-word
sum, with its genuine zero-weight integer summand and positive MW terms.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace Verification.PathOriginalDegreeTerms
open Classical CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathCochains Verification.PathCompression Verification.PathNormalizedBasis
open Verification.PathEndpointWords Verification.PathActualWordIndices
open Verification.PathOriginalIndependence Verification.PathStrictTermIndices
attribute [local instance] Abelian.hasFiniteBiproducts
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R] [Nontrivial R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (Z : A) (M : ℤ → A)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (S : StrictTorusSymbolInput.Standard J L G R T Z M site N W V)

def wordObject {n : ℕ} {B : List Bool → Prop} (x : NormalIndex B n) : A :=
  if PathWeightFiltration.weight x=0 then Z else M (PathWeightFiltration.weight x)

section Y
variable (a p : ℕ)
local notation "B" => PathOriginalYPresentation.matrix (2*a)
local notation "hf" => fun I hI => (PathOriginalAS.y a I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y a I hI).2

def yLocal (I : {I : Config (2*a) // I.val.card=p}) :
    (StrictLocalizedCells.localCell J L G R T Empty (2*a) B
      (positive_order B y_mutable) (negative_order B y_mutable) (support B y_mutable) hf hs
      p (configDegree B y_mutable p I)).term ≅
    ⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p))
      (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)) := by
  rcases I with ⟨I,hI⟩
  subst p
  exact OriginalStrictProjectionDetection.splitSource J L G R T (Empty) (2*a) B
    (positive_order B y_mutable) (negative_order B y_mutable) (support B y_mutable) hf hs
    I.val.card (configDegree B y_mutable I.val.card ⟨I,rfl⟩)
    I.val (PathEvenEndpointTorus.FreeCoordinates I.property) (PathOriginalStrictCells.yBase R I.property)
    site M N V Z W S

def yWordsIso :
    (⨁ fun I : {I : Config (2*a) // I.val.card=p} =>
      ⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p))
        (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property))) ≅
    ⨁ fun x : {x : NormalIndex BothNormal (2*a) // -(PathStratumGrading.degree x)= -(p:ℤ)} =>
      wordObject Z M x.val :=
  biproductBiproductIso _ _ ≪≫ biproduct.whiskerEquiv (yWords a p) (fun x => eqToIso (by
    change (if PathWeightFiltration.weight (yIndexEquiv a ⟨x.1.val,x.2⟩)=0 then Z
      else M (PathWeightFiltration.weight (yIndexEquiv a ⟨x.1.val,x.2⟩):ℤ))=_
    unfold StrictTorusSymbolInput.summand
    have h := y_weight x.1.val x.2
    simp only [x.1.property] at h
    rw [← h]
    simp only [Nat.cast_eq_zero]))

def yLayer :
    (⨁ fun i : ActualCellThom.Index Empty (2*a) B p =>
      (StrictLocalizedCells.localCell J L G R T Empty (2*a) B
        (positive_order B y_mutable) (negative_order B y_mutable) (support B y_mutable) hf hs p i).term) ≅
    ⨁ fun x : {x : NormalIndex BothNormal (2*a) // -(PathStratumGrading.degree x)= -(p:ℤ)} =>
      wordObject Z M x.val :=
  (biproduct.whiskerEquiv (configDegree B y_mutable p)
    (fun I => yLocal J L G R T Z M site N W V S a p I)).symm ≪≫ yWordsIso Z M a p
end Y

section Z
variable (n p : ℕ)
local notation "B" => PathOriginalZPresentation.matrix n
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2

def zLocal (I : {I : Config n // I.val.card=p}) :
    (StrictLocalizedCells.localCell J L G R T (Fin 1) n B
      (positive_order B z_mutable) (negative_order B z_mutable) (support B z_mutable) hf hs
      p (configDegree B z_mutable p I)).term ≅
    ⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p))
      (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)) := by
  rcases I with ⟨I,hI⟩
  subst p
  exact OriginalStrictProjectionDetection.splitSource J L G R T (Fin 1) (n) B
    (positive_order B z_mutable) (negative_order B z_mutable) (support B z_mutable) hf hs
    I.val.card (configDegree B z_mutable I.val.card ⟨I,rfl⟩)
    I.val (PathVariableEndpointMaps.FreeCoordinates I.property) (PathOriginalStrictCells.zBase R I.property)
    site M N V Z W S

def zWordsIso :
    (⨁ fun I : {I : Config n // I.val.card=p} =>
      ⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p))
        (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property))) ≅
    ⨁ fun x : {x : NormalIndex RightNormal n // -(PathStratumGrading.degree x)= -(p:ℤ)} =>
      wordObject Z M x.val :=
  biproductBiproductIso _ _ ≪≫ biproduct.whiskerEquiv (zWords n p) (fun x => eqToIso (by
    change (if PathWeightFiltration.weight (zIndexEquiv n ⟨x.1.val,x.2⟩)=0 then Z
      else M (PathWeightFiltration.weight (zIndexEquiv n ⟨x.1.val,x.2⟩):ℤ))=_
    unfold StrictTorusSymbolInput.summand
    have h := z_weight x.1.val x.2
    simp only [x.1.property] at h
    rw [← h]
    simp only [Nat.cast_eq_zero]))

def zLayer :
    (⨁ fun i : ActualCellThom.Index (Fin 1) n B p =>
      (StrictLocalizedCells.localCell J L G R T (Fin 1) n B
        (positive_order B z_mutable) (negative_order B z_mutable) (support B z_mutable) hf hs p i).term) ≅
    ⨁ fun x : {x : NormalIndex RightNormal n // -(PathStratumGrading.degree x)= -(p:ℤ)} =>
      wordObject Z M x.val :=
  (biproduct.whiskerEquiv (configDegree B z_mutable p)
    (fun I => zLocal J L G R T Z M site N W V S n p I)).symm ≪≫ zWordsIso Z M n p
end Z
#print axioms wordObject
#print axioms yLocal
#print axioms yWordsIso
#print axioms yLayer
#print axioms zLocal
#print axioms zWordsIso
#print axioms zLayer
end Verification.PathOriginalDegreeTerms
