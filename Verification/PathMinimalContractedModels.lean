/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalStrictComplex
import Verification.ContractedModelTransport
import Verification.PathOriginalZEquivalence

/-!
# Path Minimal Contracted Models

The genuine original Y and Z path strict models are isomorphic to their fully proved full-rho complexes and contract to the exact degree-zero MW survivors. No geometric comparison is an input.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathMinimalContractedModels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local instance] Abelian.hasFiniteBiproducts
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasFiniteBiproducts Z]
variable [HasZeroObject Z] [HasShift Z ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive] [Pretriangulated Z]
variable (J : DerivedCategory A ⥤ Z) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ Z) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)

open Verification.PathCompression Verification.PathOriginalStratumTransport
open Verification.PathOriginalIndependence Verification.PathSignedFaceUnits
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
open Verification.PathMilnorWittCoefficients
variable (R : Type) [CommRing R] [Nontrivial R]
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (QO : GradedMilnorWittThomOrientation.Normalization J L G R site M N V O W)
variable (MW : GradedMilnorWittLaurent.Standard R site N W Cg)

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (CR : StrictProjectiveModel.ChainRepresentability (A:=A))
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))
variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (Norm : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] [DecidableEq ι] (v : ι) (r : ℕ)
  (hr : Fintype.card (CoordinateFlag.Old ι v)=r),
  StandardThomContractionNormalization.Standard J L G R site M N V hV H
    (CoordinateFlag.Old ι v) r hr (K.principal ι v) Cg)

variable (Z₀ : A) (Symbols : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

variable (PH : GradedMilnorWittHomogeneity.Standard site N W)
variable (SC : GradedMilnorWittStrictScalars.Standard J L G R site M N W PH V)


section Y
variable (d : ℕ)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "hf" => fun I hI => (PathOriginalAS.y d I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y d I hI).2
local notation "Model" => OriginalPositiveCellular.model J L G R T (Empty) (2*d) B pos neg supp hf hs E P CR empty

def yOriginal : ContractedStrictProductInput.ContractedModel J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R (Empty) (2*d) B))))))
    (Z₀ ⊞ ⨁ fun k : Fin (d)=>M ((2*(k.val+1):ℕ):ℤ)) where
  model := Model
  upper := OriginalPositiveCellular.support_upper J L G R T (Empty) (2*d) B pos neg supp hf hs E P CR empty
  contraction := PathOriginalStrictComplex.yContraction J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC d

def y : ContractedStrictProductInput.ContractedModel J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (PathPresentation.PathAlgebra (2*d) (1:R) 1))))))
    (Z₀ ⊞ ⨁ fun k : Fin (d)=>M ((2*(k.val+1):ℕ):ℤ)) :=
  ContractedModelTransport.ring J L G (PathOriginalYPresentation.presentationEquiv R (2*d)).toRingEquiv
    (yOriginal J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC d)
#print axioms yOriginal
#print axioms y
end Y

section Z
variable (n : ℕ)
local notation "B" => PathOriginalZPresentation.matrix (n)
local notation "pos" => positive_order B z_mutable
local notation "neg" => negative_order B z_mutable
local notation "supp" => support B z_mutable
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2
local notation "Model" => OriginalPositiveCellular.model J L G R T (Fin 1) (n) B pos neg supp hf hs E P CR empty

def zOriginal : ContractedStrictProductInput.ContractedModel J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R (Fin 1) (n) B))))))
    (Z₀ ⊞ ⨁ fun k : Fin (n+1)=>M ((k.val+1:ℕ):ℤ)) where
  model := Model
  upper := OriginalPositiveCellular.support_upper J L G R T (Fin 1) (n) B pos neg supp hf hs E P CR empty
  contraction := PathOriginalStrictComplex.zContraction J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC n

def z : ContractedStrictProductInput.ContractedModel J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (PathOriginalZPresentation.Path R n))))))
    (Z₀ ⊞ ⨁ fun k : Fin (n+1)=>M ((k.val+1:ℕ):ℤ)) :=
  ContractedModelTransport.ring J L G (PathOriginalZEquivalence.equiv R n).toRingEquiv
    (zOriginal J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC n)
#print axioms zOriginal
#print axioms z
end Z

end Verification.PathMinimalContractedModels
