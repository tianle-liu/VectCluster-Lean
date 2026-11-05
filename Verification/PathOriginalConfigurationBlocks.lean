/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalModelTerms
import Verification.OriginalStrictLocalBlocks
import Verification.FiniteBiproductCoordinateBlocks

/-!
# Path Original Configuration Blocks

The literal original path differential in the actual configuration-indexed sums has exactly its transported geometric local blocks.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace Verification.PathOriginalConfigurationBlocks
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
    ⨁ fun I : {I : PathCochains.Config (2*a) // I.val.card=p} =>
      ⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)) :=
  OriginalStrictCellTests.degreeIso J L G R T (Empty) (2*a) B pos neg supp hf hs E P H empty p ≪≫
    (biproduct.whiskerEquiv (PathStrictTermIndices.configDegree B y_mutable p)
      (fun I=>PathOriginalDegreeTerms.yLocal J L G R T Z M site N W V S a p I)).symm

theorem y_block (b : {I : PathCochains.Config (2*a) // I.val.card=p+1})
    (i : {I : PathCochains.Config (2*a) // I.val.card=p}) :
    biproduct.ι _ b ≫ (yDegree J L G R T Z M site N W V S E P H empty a (p+1)).inv ≫
      (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (yDegree J L G R T Z M site N W V S E P H empty a p).hom ≫ biproduct.π _ i=
    (PathOriginalDegreeTerms.yLocal J L G R T Z M site N W V S a (p+1) b).inv ≫
      OriginalStrictLocalBlocks.block J L G R T (Empty) (2*a) B pos neg supp hf hs E P H empty p
        (PathStrictTermIndices.configDegree B y_mutable (p+1) b)
        (PathStrictTermIndices.configDegree B y_mutable p i) ≫
      (PathOriginalDegreeTerms.yLocal J L G R T Z M site N W V S a p i).hom := by
  simpa only [yDegree,Iso.trans_inv,Iso.trans_hom,Iso.symm_hom,Iso.symm_inv,
    OriginalStrictLocalBlocks.block,Category.assoc] using
    FiniteBiproductCoordinateBlocks.block
      (PathStrictTermIndices.configDegree B y_mutable (p+1))
      (fun b=>PathOriginalDegreeTerms.yLocal J L G R T Z M site N W V S a (p+1) b)
      (PathStrictTermIndices.configDegree B y_mutable p)
      (fun i=>PathOriginalDegreeTerms.yLocal J L G R T Z M site N W V S a p i)
      ((OriginalStrictCellTests.degreeIso J L G R T (Empty) (2*a) B pos neg supp hf hs E P H empty (p+1)).inv ≫
        (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (OriginalStrictCellTests.degreeIso J L G R T (Empty) (2*a) B pos neg supp hf hs E P H empty p).hom) b i

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

def zDegree : (Model).complex.X (-(p:ℤ)) ≅
    ⨁ fun I : {I : PathCochains.Config (n) // I.val.card=p} =>
      ⨁ StrictTorusSymbolInput.summand Z M (Fintype.card (Fin p)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)) :=
  OriginalStrictCellTests.degreeIso J L G R T (Fin 1) (n) B pos neg supp hf hs E P H empty p ≪≫
    (biproduct.whiskerEquiv (PathStrictTermIndices.configDegree B z_mutable p)
      (fun I=>PathOriginalDegreeTerms.zLocal J L G R T Z M site N W V S n p I)).symm

theorem z_block (b : {I : PathCochains.Config (n) // I.val.card=p+1})
    (i : {I : PathCochains.Config (n) // I.val.card=p}) :
    biproduct.ι _ b ≫ (zDegree J L G R T Z M site N W V S E P H empty n (p+1)).inv ≫
      (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (zDegree J L G R T Z M site N W V S E P H empty n p).hom ≫ biproduct.π _ i=
    (PathOriginalDegreeTerms.zLocal J L G R T Z M site N W V S n (p+1) b).inv ≫
      OriginalStrictLocalBlocks.block J L G R T (Fin 1) (n) B pos neg supp hf hs E P H empty p
        (PathStrictTermIndices.configDegree B z_mutable (p+1) b)
        (PathStrictTermIndices.configDegree B z_mutable p i) ≫
      (PathOriginalDegreeTerms.zLocal J L G R T Z M site N W V S n p i).hom := by
  simpa only [zDegree,Iso.trans_inv,Iso.trans_hom,Iso.symm_hom,Iso.symm_inv,
    OriginalStrictLocalBlocks.block,Category.assoc] using
    FiniteBiproductCoordinateBlocks.block
      (PathStrictTermIndices.configDegree B z_mutable (p+1))
      (fun b=>PathOriginalDegreeTerms.zLocal J L G R T Z M site N W V S n (p+1) b)
      (PathStrictTermIndices.configDegree B z_mutable p)
      (fun i=>PathOriginalDegreeTerms.zLocal J L G R T Z M site N W V S n p i)
      ((OriginalStrictCellTests.degreeIso J L G R T (Fin 1) (n) B pos neg supp hf hs E P H empty (p+1)).inv ≫
        (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (OriginalStrictCellTests.degreeIso J L G R T (Fin 1) (n) B pos neg supp hf hs E P H empty p).hom) b i

#print axioms zDegree
#print axioms z_block
end Z

end Verification.PathOriginalConfigurationBlocks
