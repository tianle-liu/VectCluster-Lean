/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalResidueMatrix

/-!
# Path Original Layer Word Basis

The source word coordinates of each adjacent face come from one fixed
word basis on its original stratum; only the literal zero-set cast changes.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathOriginalLayerWordBasis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedStratumCoefficients
open Verification.PathOriginalStratumTransport Verification.PathOriginalIndependence
open Verification.PathCanonicalCoefficientSection
open Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R]
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (W : GradedMilnorWittSheaf.Standard site N)

variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hK : SheafContractionNaturality.Standard R site N K)

open Verification.PathSignedFaceUnits Verification.PathMilnorWittCoefficients

section Y
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "Layer" => GlobalNormalFrame.ZeroLayer R Empty (2*d) (mutableSet (2*d) I) B
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R Empty B
local notation "Coef" => PathSignedStratumCoefficients.Coefficients R hI (1:R) 1
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))
local notation "ES" => GradedMilnorWittSheafEquiv.equiv site N W
  (S:=CommRingCat.of Coef) (T:=CommRingCat.of Fiber) (PathOriginalYCoefficient.coefficientEquiv R hI).toRingEquiv

def yBasis : (SI → W.Total (CommRingCat.of R)) ≃+ W.Total (CommRingCat.of Layer) :=
  (PathYWordBasis.basis R hI site N W K).trans
    (PathCanonicalSectionTotal.yProjection J L G R H site M N V hV W hI).symm.toAddEquiv

variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "Source" => GlobalNormalFrame.ZeroLayer R Empty (2*d)
  ((mutableSet (2*d) (insert j I)).erase (PathOriginalFaceIndex.selectedNormal (I:=I) j hj).val) B
local notation "cast" => GradedMilnorWittSheafEquiv.equiv site N W
  (S:=CommRingCat.of Layer) (T:=CommRingCat.of Source)
  (OriginalZeroLayerCast.equiv R Empty (2*d) B (PathOriginalFaceIndex.mutable_erase j hj ha).symm).toRingEquiv

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem y_source (f : SI → W.Total (CommRingCat.of R)) :
    PathOriginalResidueMatrix.ySourceBasis J L G R H site M N V hV W K hI j hj ha f=
      (cast) (yBasis J L G R H site M N V hV W K hI f) := by
  change (cast) ((PathCanonicalSectionTotal.yProjection J L G R H site M N V hV W hI).symm
    ((ES) ((ES).symm (PathYWordBasis.basis R hI site N W K f))))=_
  rw [RingEquiv.apply_symm_apply]
  rfl

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem y_source_inverse (a : W.Total (CommRingCat.of Layer)) :
    (PathOriginalResidueMatrix.ySourceBasis J L G R H site M N V hV W K hI j hj ha).symm
      ((cast) a)=(yBasis J L G R H site M N V hV W K hI).symm a := by
  apply (PathOriginalResidueMatrix.ySourceBasis J L G R H site M N V hV W K hI j hj ha).injective
  rw [AddEquiv.apply_symm_apply,y_source,AddEquiv.apply_symm_apply]

#print axioms yBasis
#print axioms y_source
#print axioms y_source_inverse
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
local notation "B" => PathOriginalZPresentation.matrix n
local notation "Layer" => GlobalNormalFrame.ZeroLayer R (Fin 1) n (mutableSet n I) B
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) B
local notation "Coef" => PathSignedStratumCoefficients.Coefficients (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))
local notation "ES" => GradedMilnorWittSheafEquiv.equiv site N W
  (S:=CommRingCat.of Coef) (T:=CommRingCat.of Fiber) (PathOriginalZCoefficient.coefficientEquiv R hI).toRingEquiv

def zBasis : (SI → W.Total (CommRingCat.of R)) ≃+ W.Total (CommRingCat.of Layer) :=
  (PathZWordBasis.basis R hI site N W K).trans
    (PathCanonicalSectionTotal.zProjection J L G R H site M N V hV W hI).symm.toAddEquiv

variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "Source" => GlobalNormalFrame.ZeroLayer R (Fin 1) n
  ((mutableSet n (insert j I)).erase (PathOriginalFaceIndex.selectedNormal (I:=I) j hj).val) B
local notation "cast" => GradedMilnorWittSheafEquiv.equiv site N W
  (S:=CommRingCat.of Layer) (T:=CommRingCat.of Source)
  (OriginalZeroLayerCast.equiv R (Fin 1) n B (PathOriginalFaceIndex.mutable_erase j hj ha).symm).toRingEquiv

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem z_source (f : SI → W.Total (CommRingCat.of R)) :
    PathOriginalResidueMatrix.zSourceBasis J L G R H site M N V hV W K hI j hj ha f=
      (cast) (zBasis J L G R H site M N V hV W K hI f) := by
  change (cast) ((PathCanonicalSectionTotal.zProjection J L G R H site M N V hV W hI).symm
    ((ES) ((ES).symm (PathZWordBasis.basis R hI site N W K f))))=_
  rw [RingEquiv.apply_symm_apply]
  rfl

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem z_source_inverse (a : W.Total (CommRingCat.of Layer)) :
    (PathOriginalResidueMatrix.zSourceBasis J L G R H site M N V hV W K hI j hj ha).symm
      ((cast) a)=(zBasis J L G R H site M N V hV W K hI).symm a := by
  apply (PathOriginalResidueMatrix.zSourceBasis J L G R H site M N V hV W K hI j hj ha).injective
  rw [AddEquiv.apply_symm_apply,z_source,AddEquiv.apply_symm_apply]

#print axioms zBasis
#print axioms z_source
#print axioms z_source_inverse
end Z

end Verification.PathOriginalLayerWordBasis
