/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalFullWordResidue
import Verification.PathActualOrderedWordComparison
import Verification.PathOrderedEndpointEvaluation

/-!
# Path Actual Basis Columns

Genuine Y/Z torus basis vectors, with arbitrary base coefficients, have
exactly the normalized full-rho path face columns under actual residues.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathActualBasisColumns
open Classical CategoryTheory AlgebraicGeometry Finset
open Verification.PathCompression Verification.PathSignedStratumCoefficients
open Verification.PathSignedFaceUnits Verification.PathOrderedFaceUnits
open Verification.PathMilnorWittWordFace Verification.PathActualWordIndices

theorem target_length {n : ℕ} {I : Finset ℕ}
    (j : ℕ) (hj : j∈Icc 1 n) (ha : Addable I j) (bits : List Bool)
    (hb : bits.length=(available I (n+2)).card) :
    PathRhoWords.faceColumn (-PathCoefficientRing.g) PathCoefficientRing.rho (faceIndex I j) bits ∈
      PathRhoFinite.layer (R:=PathCoefficientRing.Coeff) (available (insert j I) (n+2)).card := by
  have he := available_insert_card I j (n+2) ha (by have hh:=mem_Icc.mp hj;omega)
  have hh := PathRhoFinite.column_mem_layer (-PathCoefficientRing.g) PathCoefficientRing.rho
    (faceIndex I j) (available I (n+2)).card bits hb
  simpa only [show (available I (n+2)).card-2=(available (insert j I) (n+2)).card by omega] using hh

section Y
variable (R : Type) [CommRing R] {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
variable (j : ℕ) (hj : j∈Icc 1 (2*d)) (ha : Addable I j)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "Base" => R
local notation "a" => (1:R)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Old" => Coefficients Base hI a 1
local notation "New" => Coefficients Base (nextAdmissible hI j hj ha) a 1
local notation "Source" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Empty) (PathOriginalYPresentation.matrix (2*d))
local notation "DN" => D.symbols (CommRingCat.of New)
variable (i : BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)))
local notation "wordIndex" => yWordEquiv hI i
include P

theorem y_column (c : D.Total (CommRingCat.of R)) :
    PathOriginalYWordResidue.residue R hI j hj ha site N D K
      (GradedMilnorWittSheaf.pullback site N D (S:=CommRingCat.of Source) (T:=CommRingCat.of Old)
        (PathOriginalYCoefficient.coefficientEquiv R hI).symm.toRingHom
          (PathYWordBasis.basis R hI site N D K (Pi.single i c)))=
      ((DN).g^(j/2) * evaluate DN (units Base hJ a 1) (PathLeftEndpoint.projection (0:PathCoefficientRing.Coeff) (PathRightEndpoint.projection (PathEndpointComplex.endpointConstant PathCoefficientRing.rho (2*d)) (PathRhoWords.faceColumn (-PathCoefficientRing.g) PathCoefficientRing.rho (faceIndex I j) (wordIndex).val)))) *
        GradedMilnorWittScalarNaturality.scalar R New site N D c := by
  have hc := GradedMilnorWittScalarNaturality.naturality R Source Old site N D
    (PathOriginalYCoefficient.coefficientEquiv R hI).symm.toAlgHom c
  change GradedMilnorWittSheaf.pullback site N D (S:=CommRingCat.of Source) (T:=CommRingCat.of Old)
    (PathOriginalYCoefficient.coefficientEquiv R hI).symm.toRingHom
      (GradedMilnorWittScalarNaturality.scalar R Source site N D c)=_ at hc
  rw [PathYWordBasis.basis_single R hI site N D K P,map_mul,hc,
    PathActualOrderedWordComparison.y_word R site N D hI i]
  rw [PathOrderedEndpointEvaluation.both_projection Base hJ DN _
    (target_length j hj ha (wordIndex).val (wordIndex).property.1)]
  exact PathOriginalFullWordResidue.y_word_scalar R hI j hj ha site N D K P
    (wordIndex).val (wordIndex).property.1 c
end Y

section Z
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible (n) I)
variable (j : ℕ) (hj : j∈Icc 1 (n)) (ha : Addable I j)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "Base" => LaurentBasepoint.Laurent R
local notation "a" => (LaurentPolynomialUniversal.parameter R)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Old" => Coefficients Base hI a 1
local notation "New" => Coefficients Base (nextAdmissible hI j hj ha) a 1
local notation "Source" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) (PathOriginalZPresentation.matrix (n))
local notation "DN" => D.symbols (CommRingCat.of New)
variable (i : BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)))
local notation "wordIndex" => zWordEquiv hI i
include P

theorem z_column (c : D.Total (CommRingCat.of R)) :
    PathOriginalZWordResidue.residue R hI j hj ha site N D K
      (GradedMilnorWittSheaf.pullback site N D (S:=CommRingCat.of Source) (T:=CommRingCat.of Old)
        (PathOriginalZCoefficient.coefficientEquiv R hI).symm.toRingHom
          (PathZWordBasis.basis R hI site N D K (Pi.single i c)))=
      ((DN).g^(j/2) * evaluate DN (units Base hJ a 1) (PathRightEndpoint.projection (PathEndpointComplex.endpointConstant PathCoefficientRing.rho (n)) (PathRhoWords.faceColumn (-PathCoefficientRing.g) PathCoefficientRing.rho (faceIndex I j) (wordIndex).val))) *
        GradedMilnorWittScalarNaturality.scalar R New site N D c := by
  have hc := GradedMilnorWittScalarNaturality.naturality R Source Old site N D
    (PathOriginalZCoefficient.coefficientEquiv R hI).symm.toAlgHom c
  change GradedMilnorWittSheaf.pullback site N D (S:=CommRingCat.of Source) (T:=CommRingCat.of Old)
    (PathOriginalZCoefficient.coefficientEquiv R hI).symm.toRingHom
      (GradedMilnorWittScalarNaturality.scalar R Source site N D c)=_ at hc
  rw [PathZWordBasis.basis_single R hI site N D K P,map_mul,hc,
    PathActualOrderedWordComparison.z_word R site N D hI i]
  rw [PathOrderedEndpointEvaluation.right_projection Base hJ a DN _
    (target_length j hj ha (wordIndex).val (wordIndex).property.1)]
  exact PathOriginalFullWordResidue.z_word_scalar R hI j hj ha site N D K P
    (wordIndex).val (wordIndex).property.1 c
end Z

#print axioms target_length
#print axioms y_column
#print axioms z_column
end Verification.PathActualBasisColumns
