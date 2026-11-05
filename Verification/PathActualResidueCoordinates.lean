/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualNormalizedExpansion
import Verification.PathActualBasisColumns
import Verification.PathLiteralEntries

/-!
# Path Actual Residue Coordinates

The actual Y/Z face residue, conjugated by the constructed torus section
bases, has the literal projected full-rho coefficient entries.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
namespace Verification.PathActualResidueCoordinates
open Classical CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedStratumCoefficients
open Verification.PathSignedFaceUnits Verification.PathMilnorWittCoefficients
open Verification.PathActualWordIndices Verification.PathNormalizedBasis Verification.PathEndpointWords

section Y
variable (R : Type) [CommRing R] {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "Base" => R
local notation "a" => (1:R)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Old" => Coefficients Base hI a 1
local notation "New" => Coefficients Base (nextAdmissible hI j hj ha) a 1
local notation "Source" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Empty) (PathOriginalYPresentation.matrix (2*d))
local notation "Target" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R (Empty) (PathOriginalYPresentation.matrix (2*d))
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates (nextAdmissible hI j hj ha)))

def yColumn (i : SI) : List Bool →₀ PathCoefficientRing.Coeff := PathLeftEndpoint.projection 0 (PathLiteralEntries.projectedFace PathCoefficientRing.g PathCoefficientRing.rho (2*d) (faceIndex I j) (yWordEquiv hI i).val)

include hj ha in
theorem yColumn_normal (i : SI) : yColumn hI j i∈
    normalLayer (R:=PathCoefficientRing.Coeff) BothNormal (available (insert j I) (2*d+2)).card := by
  have hh := PathActualBasisColumns.target_length j hj ha (yWordEquiv hI i).val (yWordEquiv hI i).property.1
  exact normal_map BothNormal ((PathLeftEndpoint.projection 0).comp
    (PathRightEndpoint.projection (PathEndpointComplex.endpointConstant PathCoefficientRing.rho (2*d))))
    (PathEndpointBasis.both_column_normal 0 _)
    (available (insert j I) (2*d+2)).card _ hh

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
local notation "DR" => D.symbols (CommRingCat.of R)
local notation "ES" => GradedMilnorWittSheafEquiv.equiv site N D
  (S:=CommRingCat.of Old) (T:=CommRingCat.of Source) (PathOriginalYCoefficient.coefficientEquiv R hI).toRingEquiv
local notation "ET" => GradedMilnorWittSheafEquiv.equiv site N D
  (S:=CommRingCat.of New) (T:=CommRingCat.of Target) (PathOriginalYCoefficient.coefficientEquiv R (nextAdmissible hI j hj ha)).toRingEquiv

def yFace : (SI → D.Total (CommRingCat.of R)) →+ (TI → D.Total (CommRingCat.of R)) :=
  (PathYWordBasis.basis R hJ site N D K).symm.toAddMonoidHom.comp
    ((ET).toAddEquiv.toAddMonoidHom.comp
      ((PathOriginalYWordResidue.residue R hI j hj ha site N D K).comp
        ((ES).symm.toAddEquiv.toAddMonoidHom.comp (PathYWordBasis.basis R hI site N D K).toAddMonoidHom)))

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem yFace_single (i : SI) (c : D.Total (CommRingCat.of R)) (k : TI) :
    yFace R hI j hj ha site N D K (Pi.single i c) k=
      (DR).g^(j/2) * realize (DR).toCoefficients (yColumn hI j i (yWordEquiv hJ k).val) * c := by
  have h₁ := PathActualBasisColumns.y_column R hI j hj ha site N D K P i c
  have h₂ := PathActualNormalizedExpansion.y_expansion R hJ site N D K P
    (yColumn hI j i) (yColumn_normal hI j hj ha i) (j/2) c
  have he : PathOriginalYWordResidue.residue R hI j hj ha site N D K
      ((ES).symm (PathYWordBasis.basis R hI site N D K (Pi.single i c)))=
      (ET).symm (PathYWordBasis.basis R hJ site N D K
        (fun k => (DR).g^(j/2)*realize (DR).toCoefficients (yColumn hI j i (yWordEquiv hJ k).val)*c)) := h₁.trans h₂.symm
  change (PathYWordBasis.basis R hJ site N D K).symm
    ((ET) (PathOriginalYWordResidue.residue R hI j hj ha site N D K
      ((ES).symm (PathYWordBasis.basis R hI site N D K (Pi.single i c))))) k=_
  rw [he,RingEquiv.apply_symm_apply,AddEquiv.symm_apply_apply]
end Y

section Z
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible (n) I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (n)) (ha : Addable I j)
local notation "Base" => LaurentBasepoint.Laurent R
local notation "a" => (LaurentPolynomialUniversal.parameter R)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Old" => Coefficients Base hI a 1
local notation "New" => Coefficients Base (nextAdmissible hI j hj ha) a 1
local notation "Source" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) (PathOriginalZPresentation.matrix (n))
local notation "Target" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R (Fin 1) (PathOriginalZPresentation.matrix (n))
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates (nextAdmissible hI j hj ha)))

def zColumn (i : SI) : List Bool →₀ PathCoefficientRing.Coeff := PathLiteralEntries.projectedFace PathCoefficientRing.g PathCoefficientRing.rho (n) (faceIndex I j) (zWordEquiv hI i).val

include hj ha in
theorem zColumn_normal (i : SI) : zColumn hI j i∈
    normalLayer (R:=PathCoefficientRing.Coeff) RightNormal (available (insert j I) (n+2)).card := by
  have hh := PathActualBasisColumns.target_length j hj ha (zWordEquiv hI i).val (zWordEquiv hI i).property.1
  exact normal_map RightNormal (PathRightEndpoint.projection (PathEndpointComplex.endpointConstant PathCoefficientRing.rho n))
    (PathEndpointBasis.right_column_normal _)
    (available (insert j I) (n+2)).card _ hh

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
local notation "DR" => D.symbols (CommRingCat.of R)
local notation "ES" => GradedMilnorWittSheafEquiv.equiv site N D
  (S:=CommRingCat.of Old) (T:=CommRingCat.of Source) (PathOriginalZCoefficient.coefficientEquiv R hI).toRingEquiv
local notation "ET" => GradedMilnorWittSheafEquiv.equiv site N D
  (S:=CommRingCat.of New) (T:=CommRingCat.of Target) (PathOriginalZCoefficient.coefficientEquiv R (nextAdmissible hI j hj ha)).toRingEquiv

def zFace : (SI → D.Total (CommRingCat.of R)) →+ (TI → D.Total (CommRingCat.of R)) :=
  (PathZWordBasis.basis R hJ site N D K).symm.toAddMonoidHom.comp
    ((ET).toAddEquiv.toAddMonoidHom.comp
      ((PathOriginalZWordResidue.residue R hI j hj ha site N D K).comp
        ((ES).symm.toAddEquiv.toAddMonoidHom.comp (PathZWordBasis.basis R hI site N D K).toAddMonoidHom)))

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem zFace_single (i : SI) (c : D.Total (CommRingCat.of R)) (k : TI) :
    zFace R hI j hj ha site N D K (Pi.single i c) k=
      (DR).g^(j/2) * realize (DR).toCoefficients (zColumn hI j i (zWordEquiv hJ k).val) * c := by
  have h₁ := PathActualBasisColumns.z_column R hI j hj ha site N D K P i c
  have h₂ := PathActualNormalizedExpansion.z_expansion R hJ site N D K P
    (zColumn hI j i) (zColumn_normal hI j hj ha i) (j/2) c
  have he : PathOriginalZWordResidue.residue R hI j hj ha site N D K
      ((ES).symm (PathZWordBasis.basis R hI site N D K (Pi.single i c)))=
      (ET).symm (PathZWordBasis.basis R hJ site N D K
        (fun k => (DR).g^(j/2)*realize (DR).toCoefficients (zColumn hI j i (zWordEquiv hJ k).val)*c)) := h₁.trans h₂.symm
  change (PathZWordBasis.basis R hJ site N D K).symm
    ((ET) (PathOriginalZWordResidue.residue R hI j hj ha site N D K
      ((ES).symm (PathZWordBasis.basis R hI site N D K (Pi.single i c))))) k=_
  rw [he,RingEquiv.apply_symm_apply,AddEquiv.symm_apply_apply]
end Z

#print axioms yColumn
#print axioms yColumn_normal
#print axioms yFace
#print axioms yFace_single
#print axioms zColumn
#print axioms zColumn_normal
#print axioms zFace
#print axioms zFace_single
end Verification.PathActualResidueCoordinates
