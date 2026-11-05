/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualNormalComparison
import Verification.ComposedFrameDifferential
import Verification.NonpositiveComplexComparison
import Verification.PathGradedSupport

/-!
# Path Original Strict Complex

The genuine original Y and Z path strict models are isomorphic to their fully proved full-rho complexes and contract to the exact degree-zero MW survivors. No geometric comparison is an input.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathOriginalStrictComplex
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

local notation "Action" => PathStrictCoefficientAction.action J L G R site M N W PH V SC 1

section Y
variable (d : ℕ)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "hf" => fun I hI => (PathOriginalAS.y d I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y d I hI).2
local notation "Model" => OriginalPositiveCellular.model J L G R T (Empty) (2*d) B pos neg supp hf hs E P CR empty
local notation "Target" => PathGradedSheafModel.ySource (fun j:ℕ=>M (j:ℤ)) Action Z₀ d

include Q Norm hCg QO MW in
theorem y_comm (p : ℕ) :
    (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
      (PathConfigurationFramedTerms.yDegree J L G R T Z₀ M site N W V Symbols Action E P CR empty PH SC d p).hom=
    (PathConfigurationFramedTerms.yDegree J L G R T Z₀ M site N W V Symbols Action E P CR empty PH SC d (p+1)).hom ≫
      (Target).d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) := by
  simpa only [PathConfigurationFramedTerms.yDegree,PathActualWordDifferential.yDegree,
    Iso.trans_hom,Category.assoc] using
    ComposedFrameDifferential.comm
      (PathActualWordDifferential.yDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC d (p+1))
      (PathActualWordDifferential.yDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC d p)
      (PathNormalTermIso.y Z₀ (fun j:ℕ=>M (j:ℤ)) Action d (-((p+1:ℕ):ℤ)))
      (PathNormalTermIso.y Z₀ (fun j:ℕ=>M (j:ℤ)) Action d (-(p:ℤ))) _ _
      (PathActualNormalComparison.y_normal J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC d p)

def y : (Model).complex ≅ (Target) := by
  letI := OriginalPositiveCellular.support_upper J L G R T (Empty) (2*d) B pos neg supp hf hs E P CR empty
  letI := PathGradedSupport.y (fun j:ℕ=>M (j:ℤ)) Action Z₀ d
  exact NonpositiveComplexComparison.iso (Model).complex (Target)
    (PathConfigurationFramedTerms.yDegree J L G R T Z₀ M site N W V Symbols Action E P CR empty PH SC d)
    (y_comm J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC d)

def yContraction : HomotopyEquiv (Model).complex
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj
      (Z₀ ⊞ ⨁ fun k : Fin (d)=>M ((2*(k.val+1):ℕ):ℤ))) :=
  (HomotopyEquiv.ofIso (y J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC d)).trans
    (PathGradedSheafModel.yEquivalence (fun j:ℕ=>M (j:ℤ)) Action Z₀ d)

#print axioms y_comm
#print axioms y
#print axioms yContraction
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
local notation "Target" => PathGradedSheafModel.zSource (fun j:ℕ=>M (j:ℤ)) Action Z₀ n

include Q Norm hCg QO MW in
theorem z_comm (p : ℕ) :
    (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
      (PathConfigurationFramedTerms.zDegree J L G R T Z₀ M site N W V Symbols Action E P CR empty PH SC n p).hom=
    (PathConfigurationFramedTerms.zDegree J L G R T Z₀ M site N W V Symbols Action E P CR empty PH SC n (p+1)).hom ≫
      (Target).d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) := by
  simpa only [PathConfigurationFramedTerms.zDegree,PathActualWordDifferential.zDegree,
    Iso.trans_hom,Category.assoc] using
    ComposedFrameDifferential.comm
      (PathActualWordDifferential.zDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC n (p+1))
      (PathActualWordDifferential.zDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC n p)
      (PathNormalTermIso.z Z₀ (fun j:ℕ=>M (j:ℤ)) Action n (-((p+1:ℕ):ℤ)))
      (PathNormalTermIso.z Z₀ (fun j:ℕ=>M (j:ℤ)) Action n (-(p:ℤ))) _ _
      (PathActualNormalComparison.z_normal J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC n p)

def z : (Model).complex ≅ (Target) := by
  letI := OriginalPositiveCellular.support_upper J L G R T (Fin 1) (n) B pos neg supp hf hs E P CR empty
  letI := PathGradedSupport.z (fun j:ℕ=>M (j:ℤ)) Action Z₀ n
  exact NonpositiveComplexComparison.iso (Model).complex (Target)
    (PathConfigurationFramedTerms.zDegree J L G R T Z₀ M site N W V Symbols Action E P CR empty PH SC n)
    (z_comm J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC n)

def zContraction : HomotopyEquiv (Model).complex
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj
      (Z₀ ⊞ ⨁ fun k : Fin (n+1)=>M ((k.val+1:ℕ):ℤ))) :=
  (HomotopyEquiv.ofIso (z J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC n)).trans
    (PathGradedSheafModel.zEquivalence (fun j:ℕ=>M (j:ℤ)) Action Z₀ n)

#print axioms z_comm
#print axioms z
#print axioms zContraction
end Z

end Verification.PathOriginalStrictComplex
