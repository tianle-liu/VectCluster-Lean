/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalResidueTransport
import Verification.PathActualResidueMatrix

/-!
# Path Original Residue Matrix

Every genuine original path-source section, in the actual Laurent word
basis, has the computed full-rho adjacent residue matrix.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Verification.PathOriginalResidueMatrix
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
variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Coef" => Coefficients R hI (1:R) 1
local notation "NewCoef" => Coefficients R hJ (1:R) 1
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R Empty B
local notation "New" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R Empty B
local notation "Source" => GlobalNormalFrame.ZeroLayer R Empty (2*d)
  ((mutableSet (2*d) (insert j I)).erase (PathOriginalFaceIndex.selectedNormal (I:=I) j hj).val) B
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ))
local notation "ES" => GradedMilnorWittSheafEquiv.equiv site N W
  (S:=CommRingCat.of Coef) (T:=CommRingCat.of Fiber) (PathOriginalYCoefficient.coefficientEquiv R hI).toRingEquiv
local notation "ET" => GradedMilnorWittSheafEquiv.equiv site N W
  (S:=CommRingCat.of NewCoef) (T:=CommRingCat.of New) (PathOriginalYCoefficient.coefficientEquiv R hJ).toRingEquiv

def ySourceBasis : (SI → W.Total (CommRingCat.of R)) ≃+ W.Total (CommRingCat.of Source) :=
  ((PathYWordBasis.basis R hI site N W K).trans (ES).symm.toAddEquiv).trans
    (PathCanonicalSectionTotal.ySourceCoordinates J L G R H site M N V hV W hI j hj ha).toAddEquiv

include hK in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem y_face (f : SI → W.Total (CommRingCat.of R)) :
    (PathYWordBasis.basis R hJ site N W K).symm
      (PathOriginalResidueTransport.yResidue R site N W K hI j hj ha
        (ySourceBasis J L G R H site M N V hV W K hI j hj ha f))=
      PathActualResidueCoordinates.yFace R hI j hj ha site N W K f := by
  have hh := PathOriginalResidueTransport.y_coordinates J L G R H site M N V hV W K hK hI j hj ha
    ((ES).symm (PathYWordBasis.basis R hI site N W K f))
  change (ET).symm (PathOriginalResidueTransport.yResidue R site N W K hI j hj ha
    (ySourceBasis J L G R H site M N V hV W K hI j hj ha f))=
      PathOriginalYWordResidue.residue R hI j hj ha site N W K
        ((ES).symm (PathYWordBasis.basis R hI site N W K f)) at hh
  change _=(PathYWordBasis.basis R hJ site N W K).symm ((ET)
    (PathOriginalYWordResidue.residue R hI j hj ha site N W K
      ((ES).symm (PathYWordBasis.basis R hI site N W K f))))
  rw [←hh,RingEquiv.apply_symm_apply]

variable (P : GradedMilnorWittLaurent.Standard R site N W K)
include hK P in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem y_matrix (a : W.Total (CommRingCat.of Source)) (k : TI) :
    (PathYWordBasis.basis R hJ site N W K).symm
      (PathOriginalResidueTransport.yResidue R site N W K hI j hj ha a) k=
    ∑ i : SI, ((W.symbols (CommRingCat.of R)).g^(j/2)*
      realize (W.symbols (CommRingCat.of R)).toCoefficients
        (PathActualResidueCoordinates.yColumn hI j i (PathActualWordIndices.yWordEquiv hJ k).val))*
      ((ySourceBasis J L G R H site M N V hV W K hI j hj ha).symm a) i := by
  have hh := congrFun (y_face J L G R H site M N V hV W K hK hI j hj ha
    ((ySourceBasis J L G R H site M N V hV W K hI j hj ha).symm a)) k
  rw [AddEquiv.apply_symm_apply,PathActualResidueMatrix.y_apply R hI j hj ha site N W K P] at hh
  exact hh

#print axioms ySourceBasis
#print axioms y_face
#print axioms y_matrix
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "B" => PathOriginalZPresentation.matrix n
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Coef" => Coefficients (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1
local notation "NewCoef" => Coefficients (PathOriginalZPresentation.Coefficient R) hJ (LaurentPolynomialUniversal.parameter R) 1
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) B
local notation "New" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R (Fin 1) B
local notation "Source" => GlobalNormalFrame.ZeroLayer R (Fin 1) n
  ((mutableSet n (insert j I)).erase (PathOriginalFaceIndex.selectedNormal (I:=I) j hj).val) B
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ))
local notation "ES" => GradedMilnorWittSheafEquiv.equiv site N W
  (S:=CommRingCat.of Coef) (T:=CommRingCat.of Fiber) (PathOriginalZCoefficient.coefficientEquiv R hI).toRingEquiv
local notation "ET" => GradedMilnorWittSheafEquiv.equiv site N W
  (S:=CommRingCat.of NewCoef) (T:=CommRingCat.of New) (PathOriginalZCoefficient.coefficientEquiv R hJ).toRingEquiv

def zSourceBasis : (SI → W.Total (CommRingCat.of R)) ≃+ W.Total (CommRingCat.of Source) :=
  ((PathZWordBasis.basis R hI site N W K).trans (ES).symm.toAddEquiv).trans
    (PathCanonicalSectionTotal.zSourceCoordinates J L G R H site M N V hV W hI j hj ha).toAddEquiv

include hK in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem z_face (f : SI → W.Total (CommRingCat.of R)) :
    (PathZWordBasis.basis R hJ site N W K).symm
      (PathOriginalResidueTransport.zResidue R site N W K hI j hj ha
        (zSourceBasis J L G R H site M N V hV W K hI j hj ha f))=
      PathActualResidueCoordinates.zFace R hI j hj ha site N W K f := by
  have hh := PathOriginalResidueTransport.z_coordinates J L G R H site M N V hV W K hK hI j hj ha
    ((ES).symm (PathZWordBasis.basis R hI site N W K f))
  change (ET).symm (PathOriginalResidueTransport.zResidue R site N W K hI j hj ha
    (zSourceBasis J L G R H site M N V hV W K hI j hj ha f))=
      PathOriginalZWordResidue.residue R hI j hj ha site N W K
        ((ES).symm (PathZWordBasis.basis R hI site N W K f)) at hh
  change _=(PathZWordBasis.basis R hJ site N W K).symm ((ET)
    (PathOriginalZWordResidue.residue R hI j hj ha site N W K
      ((ES).symm (PathZWordBasis.basis R hI site N W K f))))
  rw [←hh,RingEquiv.apply_symm_apply]

variable (P : GradedMilnorWittLaurent.Standard R site N W K)
include hK P in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem z_matrix (a : W.Total (CommRingCat.of Source)) (k : TI) :
    (PathZWordBasis.basis R hJ site N W K).symm
      (PathOriginalResidueTransport.zResidue R site N W K hI j hj ha a) k=
    ∑ i : SI, ((W.symbols (CommRingCat.of R)).g^(j/2)*
      realize (W.symbols (CommRingCat.of R)).toCoefficients
        (PathActualResidueCoordinates.zColumn hI j i (PathActualWordIndices.zWordEquiv hJ k).val))*
      ((zSourceBasis J L G R H site M N V hV W K hI j hj ha).symm a) i := by
  have hh := congrFun (z_face J L G R H site M N V hV W K hK hI j hj ha
    ((zSourceBasis J L G R H site M N V hV W K hI j hj ha).symm a)) k
  rw [AddEquiv.apply_symm_apply,PathActualResidueMatrix.z_apply R hI j hj ha site N W K P] at hh
  exact hh

#print axioms zSourceBasis
#print axioms z_face
#print axioms z_matrix
end Z

end Verification.PathOriginalResidueMatrix
