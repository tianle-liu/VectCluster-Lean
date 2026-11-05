/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalConfigurationBlocks
import Verification.PathStrictFrameMatrix

/-!
# Path Configuration Framed Terms

Original path degrees in configurationwise signed frames, before and after the exact normal-word reindexing.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace Verification.PathConfigurationFramedTerms
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

omit [HasBinaryBiproducts A] [HasFiniteBiproducts D] [HasZeroObject D]
  [∀ q : ℤ, (shiftFunctor D q).Additive] [Pretriangulated D] [J.CommShift ℤ] [J.IsTriangulated]
  [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] [Nontrivial R] [HasShift D ℤ] [J.Additive] in
theorem item_inv (I : Finset ℕ) (r n : ℕ) (i : BinaryWordCoordinates.Index n) :
    (PathStrictFrameMatrix.item J L G R site M N W PH V SC Z I r n i).inv=
    (PathStrictFrameMatrix.item J L G R site M N W PH V SC Z I r n i).hom := by
  unfold PathStrictFrameMatrix.item
  split
  · rfl
  · simp only [Iso.trans_inv,Iso.trans_hom,Iso.symm_inv,Iso.symm_hom,Category.assoc]
    rfl

omit [HasBinaryBiproducts A] [HasFiniteBiproducts D] [HasZeroObject D]
  [∀ q : ℤ, (shiftFunctor D q).Additive] [Pretriangulated D] [J.CommShift ℤ] [J.IsTriangulated]
  [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] [Nontrivial R] [HasShift D ℤ] [J.Additive] in
theorem diagonal_inv (I : Finset ℕ) (r n : ℕ) :
    (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z I r n).inv=
    (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z I r n).hom := by
  simp only [PathStrictFrameMatrix.diagonal,biproduct.mapIso_inv,biproduct.mapIso_hom,item_inv]

section Y
variable (a p : ℕ)
local notation "B" => PathOriginalYPresentation.matrix (2*a)
local notation "hf" => fun I hI => (PathOriginalAS.y a I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y a I hI).2
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "Model" => OriginalPositiveCellular.model J L G R T (Empty) (2*a) B pos neg supp hf hs E P H empty

def yConfigDegree : (Model).complex.X (-(p:ℤ)) ≅
    ⨁ fun I : {I : PathCochains.Config (2*a) // I.val.card=p} =>
      ⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)) :=
  PathOriginalConfigurationBlocks.yDegree J L G R T Z M site N W V S E P H empty a p ≪≫
    biproduct.mapIso (fun I=>PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z
      I.val.val (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))

def yDegree : (Model).complex.X (-(p:ℤ)) ≅
    (PathGradedSheafModel.ySource (fun j:ℕ=>M (j:ℤ)) Action Z a).X (-(p:ℤ)) :=
  yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a p ≪≫
    PathOriginalDegreeTerms.yWordsIso Z M a p ≪≫
      PathNormalTermIso.y Z (fun j:ℕ=>M (j:ℤ)) Action a (-(p:ℤ))

theorem y_block (b : {I : PathCochains.Config (2*a) // I.val.card=p+1})
    (i : {I : PathCochains.Config (2*a) // I.val.card=p}) :
    biproduct.ι _ b ≫ (yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a (p+1)).inv ≫
      (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a p).hom ≫ biproduct.π _ i=
    (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z b.val.val
      (Fintype.card (Fin (p+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates b.val.property))).inv ≫
    ((PathOriginalDegreeTerms.yLocal J L G R T Z M site N W V S a (p+1) b).inv ≫
      OriginalStrictLocalBlocks.block J L G R T (Empty) (2*a) B pos neg supp hf hs E P H empty p
        (PathStrictTermIndices.configDegree B y_mutable (p+1) b)
        (PathStrictTermIndices.configDegree B y_mutable p i) ≫
      (PathOriginalDegreeTerms.yLocal J L G R T Z M site N W V S a p i).hom) ≫
    (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z i.val.val
      (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates i.val.property))).hom := by
  simpa only [yConfigDegree,Iso.trans_inv,Iso.trans_hom,biproduct.mapIso_inv,biproduct.mapIso_hom,
    Category.assoc,biproduct.map_π,biproduct.ι_map_assoc] using
    congrArg (fun f=>
      (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z b.val.val
        (Fintype.card (Fin (p+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates b.val.property))).inv ≫ f ≫
      (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z i.val.val
        (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates i.val.property))).hom)
      (PathOriginalConfigurationBlocks.y_block J L G R T Z M site N W V S E P H empty a p b i)

#print axioms yConfigDegree
#print axioms yDegree
#print axioms y_block
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

def zConfigDegree : (Model).complex.X (-(p:ℤ)) ≅
    ⨁ fun I : {I : PathCochains.Config (n) // I.val.card=p} =>
      ⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)) :=
  PathOriginalConfigurationBlocks.zDegree J L G R T Z M site N W V S E P H empty n p ≪≫
    biproduct.mapIso (fun I=>PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z
      I.val.val (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))

def zDegree : (Model).complex.X (-(p:ℤ)) ≅
    (PathGradedSheafModel.zSource (fun j:ℕ=>M (j:ℤ)) Action Z n).X (-(p:ℤ)) :=
  zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n p ≪≫
    PathOriginalDegreeTerms.zWordsIso Z M n p ≪≫
      PathNormalTermIso.z Z (fun j:ℕ=>M (j:ℤ)) Action n (-(p:ℤ))

theorem z_block (b : {I : PathCochains.Config (n) // I.val.card=p+1})
    (i : {I : PathCochains.Config (n) // I.val.card=p}) :
    biproduct.ι _ b ≫ (zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n (p+1)).inv ≫
      (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n p).hom ≫ biproduct.π _ i=
    (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z b.val.val
      (Fintype.card (Fin (p+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates b.val.property))).inv ≫
    ((PathOriginalDegreeTerms.zLocal J L G R T Z M site N W V S n (p+1) b).inv ≫
      OriginalStrictLocalBlocks.block J L G R T (Fin 1) (n) B pos neg supp hf hs E P H empty p
        (PathStrictTermIndices.configDegree B z_mutable (p+1) b)
        (PathStrictTermIndices.configDegree B z_mutable p i) ≫
      (PathOriginalDegreeTerms.zLocal J L G R T Z M site N W V S n p i).hom) ≫
    (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z i.val.val
      (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates i.val.property))).hom := by
  simpa only [zConfigDegree,Iso.trans_inv,Iso.trans_hom,biproduct.mapIso_inv,biproduct.mapIso_hom,
    Category.assoc,biproduct.map_π,biproduct.ι_map_assoc] using
    congrArg (fun f=>
      (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z b.val.val
        (Fintype.card (Fin (p+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates b.val.property))).inv ≫ f ≫
      (PathStrictFrameMatrix.diagonal J L G R site M N W PH V SC Z i.val.val
        (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates i.val.property))).hom)
      (PathOriginalConfigurationBlocks.z_block J L G R T Z M site N W V S E P H empty n p b i)

#print axioms zConfigDegree
#print axioms zDegree
#print axioms z_block
end Z

#print axioms item_inv
#print axioms diagonal_inv
end Verification.PathConfigurationFramedTerms
