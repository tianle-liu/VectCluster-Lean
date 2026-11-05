/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathConfigurationFramedTerms
import Verification.PathWordObjectTransport

/-!
# Path Actual Word Differential

Exact flattening of the original global signed-frame path differential to its normal-word entries.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace Verification.PathActualWordDifferential
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable [Nontrivial R]

open Verification.PathOriginalIndependence
attribute [local instance] Abelian.hasFiniteBiproducts
variable (Z : A) (M : ℤ → A)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (S : StrictTorusSymbolInput.Standard J L G R T Z M site N W V)
variable (Action : PathGradedCoefficientAction.Action (fun j=>M ((j+1:ℕ):ℤ)))
variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)
variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

variable (PH : GradedMilnorWittHomogeneity.Standard site N W)
variable (SC : GradedMilnorWittStrictScalars.Standard J L G R site M N W PH V)

section Y
variable (a p : ℕ)
local notation "B" => PathOriginalYPresentation.matrix (2*a)
local notation "hf" => fun I hI => (PathOriginalAS.y a I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y a I hI).2
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "Model" => OriginalPositiveCellular.model J L G R T (Empty) (2*a) B pos neg supp hf hs E P H empty

def yDegree : (Model).complex.X (-(p:ℤ)) ≅
    ⨁ fun x : {x : PathNormalizedBasis.NormalIndex PathEndpointWords.BothNormal (2*a) // -(PathStratumGrading.degree x)= -(p:ℤ)} =>
      PathOriginalDegreeTerms.wordObject Z M x.val :=
  PathConfigurationFramedTerms.yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a p ≪≫
    PathOriginalDegreeTerms.yWordsIso Z M a p

variable (b : Σ I : {I : PathCochains.Config (2*a) // I.val.card=p+1},
  BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
variable (i : Σ I : {I : PathCochains.Config (2*a) // I.val.card=p},
  BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))

theorem y_entry :
    biproduct.ι _ (PathStrictTermIndices.yWords a (p+1) b) ≫
      (yDegree J L G R T Z M site N W V S E P H empty PH SC a (p+1)).inv ≫
      (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
      (yDegree J L G R T Z M site N W V S E P H empty PH SC a p).hom ≫
      biproduct.π _ (PathStrictTermIndices.yWords a p i)=
    (PathWordObjectTransport.yObject Z M a (p+1) b).hom ≫
      (biproduct.ι (StrictTorusSymbolInput.summand Z M (Fintype.card (Fin (p+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates b.1.val.property))) b.2 ≫
        (biproduct.ι (fun K : {K : PathCochains.Config (2*a) // K.val.card=p+1}=>⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin (p+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates K.val.property))) b.1 ≫
          (PathConfigurationFramedTerms.yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a (p+1)).inv ≫
          (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
          (PathConfigurationFramedTerms.yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a p).hom ≫
          biproduct.π (fun K : {K : PathCochains.Config (2*a) // K.val.card=p}=>⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates K.val.property))) i.1) ≫ biproduct.π (StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates i.1.val.property))) i.2) ≫
      (PathWordObjectTransport.yObject Z M a p i).inv := by
  simpa only [yDegree,Iso.trans_inv,Iso.trans_hom,PathWordObjectTransport.y_wordsIso,Category.assoc] using
    FiniteBiproductWordEntries.entry
      (fun I : {I : PathCochains.Config (2*a) // I.val.card=p+1}=>
        BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
      (fun I=>StrictTorusSymbolInput.summand Z M (Fintype.card (Fin (p+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
      (fun x=>PathOriginalDegreeTerms.wordObject Z M x.val) (PathStrictTermIndices.yWords a (p+1))
      (PathWordObjectTransport.yObject Z M a (p+1))
      (fun I : {I : PathCochains.Config (2*a) // I.val.card=p}=>
        BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
      (fun I=>StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
      (fun x=>PathOriginalDegreeTerms.wordObject Z M x.val) (PathStrictTermIndices.yWords a p)
      (PathWordObjectTransport.yObject Z M a p)
      ((PathConfigurationFramedTerms.yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a (p+1)).inv ≫
        (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (PathConfigurationFramedTerms.yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a p).hom) b.1 b.2 i.1 i.2

#print axioms yDegree
#print axioms y_entry
end Y
section Z
variable (n p : ℕ)
local notation "B" => PathOriginalZPresentation.matrix (n)
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2
local notation "pos" => positive_order B z_mutable
local notation "neg" => negative_order B z_mutable
local notation "supp" => support B z_mutable
local notation "Model" => OriginalPositiveCellular.model J L G R T (Fin 1) (n) B pos neg supp hf hs E P H empty

def zDegree : (Model).complex.X (-(p:ℤ)) ≅
    ⨁ fun x : {x : PathNormalizedBasis.NormalIndex PathEndpointWords.RightNormal (n) // -(PathStratumGrading.degree x)= -(p:ℤ)} =>
      PathOriginalDegreeTerms.wordObject Z M x.val :=
  PathConfigurationFramedTerms.zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n p ≪≫
    PathOriginalDegreeTerms.zWordsIso Z M n p

variable (b : Σ I : {I : PathCochains.Config (n) // I.val.card=p+1},
  BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
variable (i : Σ I : {I : PathCochains.Config (n) // I.val.card=p},
  BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))

theorem z_entry :
    biproduct.ι _ (PathStrictTermIndices.zWords n (p+1) b) ≫
      (zDegree J L G R T Z M site N W V S E P H empty PH SC n (p+1)).inv ≫
      (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
      (zDegree J L G R T Z M site N W V S E P H empty PH SC n p).hom ≫
      biproduct.π _ (PathStrictTermIndices.zWords n p i)=
    (PathWordObjectTransport.zObject Z M n (p+1) b).hom ≫
      (biproduct.ι (StrictTorusSymbolInput.summand Z M (Fintype.card (Fin (p+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates b.1.val.property))) b.2 ≫
        (biproduct.ι (fun K : {K : PathCochains.Config (n) // K.val.card=p+1}=>⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin (p+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates K.val.property))) b.1 ≫
          (PathConfigurationFramedTerms.zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n (p+1)).inv ≫
          (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
          (PathConfigurationFramedTerms.zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n p).hom ≫
          biproduct.π (fun K : {K : PathCochains.Config (n) // K.val.card=p}=>⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates K.val.property))) i.1) ≫ biproduct.π (StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates i.1.val.property))) i.2) ≫
      (PathWordObjectTransport.zObject Z M n p i).inv := by
  simpa only [zDegree,Iso.trans_inv,Iso.trans_hom,PathWordObjectTransport.z_wordsIso,Category.assoc] using
    FiniteBiproductWordEntries.entry
      (fun I : {I : PathCochains.Config (n) // I.val.card=p+1}=>
        BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
      (fun I=>StrictTorusSymbolInput.summand Z M (Fintype.card (Fin (p+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
      (fun x=>PathOriginalDegreeTerms.wordObject Z M x.val) (PathStrictTermIndices.zWords n (p+1))
      (PathWordObjectTransport.zObject Z M n (p+1))
      (fun I : {I : PathCochains.Config (n) // I.val.card=p}=>
        BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
      (fun I=>StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
      (fun x=>PathOriginalDegreeTerms.wordObject Z M x.val) (PathStrictTermIndices.zWords n p)
      (PathWordObjectTransport.zObject Z M n p)
      ((PathConfigurationFramedTerms.zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n (p+1)).inv ≫
        (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (PathConfigurationFramedTerms.zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n p).hom) b.1 b.2 i.1 i.2

#print axioms zDegree
#print axioms z_entry
end Z

end Verification.PathActualWordDifferential
