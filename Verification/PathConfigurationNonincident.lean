/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathConfigurationFramedTerms
import Verification.OriginalStrictNonincidentBlock
import Verification.PathConfigurationIncidence

/-!
# Path Configuration Nonincident

Every nonincident global path configuration block vanishes in the genuine signed strict frames.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace Verification.PathConfigurationNonincident
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

theorem y_zero (b : {I : PathCochains.Config (2*a) // I.val.card=p+1})
    (i : {I : PathCochains.Config (2*a) // I.val.card=p}) (h : ¬i.val.val⊆b.val.val) :
    biproduct.ι _ b ≫ (PathConfigurationFramedTerms.yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a (p+1)).inv ≫
      (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (PathConfigurationFramedTerms.yConfigDegree J L G R T Z M site N W V S E P H empty PH SC a p).hom ≫ biproduct.π _ i=0 := by
  rw [PathConfigurationFramedTerms.y_block]
  rw [OriginalStrictNonincidentBlock.zero J L G R T (Empty) (2*a) B pos neg supp hf hs E P H empty p
    (PathStrictTermIndices.configDegree B y_mutable (p+1) b)
    (PathStrictTermIndices.configDegree B y_mutable p i)
    (fun hsub=>h ((PathConfigurationIncidence.mutable_subset i.val.property b.val.property).mp hsub))]
  simp only [comp_zero,zero_comp]

#print axioms y_zero
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

theorem z_zero (b : {I : PathCochains.Config (n) // I.val.card=p+1})
    (i : {I : PathCochains.Config (n) // I.val.card=p}) (h : ¬i.val.val⊆b.val.val) :
    biproduct.ι _ b ≫ (PathConfigurationFramedTerms.zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n (p+1)).inv ≫
      (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
        (PathConfigurationFramedTerms.zConfigDegree J L G R T Z M site N W V S E P H empty PH SC n p).hom ≫ biproduct.π _ i=0 := by
  rw [PathConfigurationFramedTerms.z_block]
  rw [OriginalStrictNonincidentBlock.zero J L G R T (Fin 1) (n) B pos neg supp hf hs E P H empty p
    (PathStrictTermIndices.configDegree B z_mutable (p+1) b)
    (PathStrictTermIndices.configDegree B z_mutable p i)
    (fun hsub=>h ((PathConfigurationIncidence.mutable_subset i.val.property b.val.property).mp hsub))]
  simp only [comp_zero,zero_comp]

#print axioms z_zero
end Z

end Verification.PathConfigurationNonincident
