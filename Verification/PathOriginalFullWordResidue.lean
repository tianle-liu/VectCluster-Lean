/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOrderedFaceResidue
import Verification.PathOriginalYWordResidue
import Verification.PathOriginalZWordResidue
import Verification.GradedMilnorWittResidueScalar

/-!
# Path Original Full Word Residue

Every actual original Y/Z coefficient word, with an arbitrary base
coefficient, realizes the literal full-rho face column.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathOriginalFullWordResidue
open CategoryTheory AlgebraicGeometry Finset
open Verification.PathCompression Verification.PathSignedStratumCoefficients
open Verification.PathSignedFaceUnits Verification.PathOrderedFaceUnits
open Verification.PathMilnorWittWordFace

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
local notation "DO" => D.symbols (CommRingCat.of Old)
local notation "DN" => D.symbols (CommRingCat.of New)
include P

theorem y_word (bits : List Bool) (hb : bits.length=(available I (2*d+2)).card) :
    PathOriginalYWordResidue.residue R hI j hj ha site N D K (wordValue DO (units Base hI a 1) bits)=
      (DN).g^(j/2) * evaluate DN (units Base hJ a 1)
        (PathRhoWords.faceColumn (-PathCoefficientRing.g) PathCoefficientRing.rho (faceIndex I j) bits) := by
  unfold PathOriginalYWordResidue.residue
  change GradedMilnorWittLaurent.residue R site N D K New (PathOriginalYWordResidue.smooth R hI j hj ha)
    (GradedMilnorWittSheaf.pullback site N D
      (S:=CommRingCat.of Old) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (PathOriginalYSignedFace.coefficientPullback R hI j hj ha).toRingHom _) = _
  rw [PathOriginalYWordResidue.pullback_eq]
  exact PathOrderedFaceResidue.full_word R Base hI a 1 j hj ha (j/2) site N D K
    (PathOriginalYWordResidue.smooth R hI j hj ha) P bits hb

theorem y_word_scalar (bits : List Bool) (hb : bits.length=(available I (2*d+2)).card)
    (c : D.Total (CommRingCat.of R)) :
    PathOriginalYWordResidue.residue R hI j hj ha site N D K
      (wordValue DO (units Base hI a 1) bits * GradedMilnorWittScalarNaturality.scalar R Old site N D c)=
      ((DN).g^(j/2) * evaluate DN (units Base hJ a 1)
        (PathRhoWords.faceColumn (-PathCoefficientRing.g) PathCoefficientRing.rho (faceIndex I j) bits)) *
          GradedMilnorWittScalarNaturality.scalar R New site N D c := by
  have he := y_word R hI j hj ha site N D K P bits hb
  unfold PathOriginalYWordResidue.residue at he ⊢
  change GradedMilnorWittLaurent.residue R site N D K New (PathOriginalYWordResidue.smooth R hI j hj ha)
    (GradedMilnorWittSheaf.pullback site N D
      (S:=CommRingCat.of Old) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (PathOriginalYSignedFace.coefficientPullback R hI j hj ha).toRingHom (_ * _)) = _
  rw [map_mul,GradedMilnorWittScalarNaturality.naturality R Old (LaurentBasepoint.Laurent New) site N D
    (PathOriginalYSignedFace.coefficientPullback R hI j hj ha),
    GradedMilnorWittResidueScalar.coefficient_mul R New site N D K
      (PathOriginalYWordResidue.smooth R hI j hj ha) P]
  exact congrArg (fun x => x * GradedMilnorWittScalarNaturality.scalar R New site N D c) he
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
local notation "DO" => D.symbols (CommRingCat.of Old)
local notation "DN" => D.symbols (CommRingCat.of New)
include P

theorem z_word (bits : List Bool) (hb : bits.length=(available I (n+2)).card) :
    PathOriginalZWordResidue.residue R hI j hj ha site N D K (wordValue DO (units Base hI a 1) bits)=
      (DN).g^(j/2) * evaluate DN (units Base hJ a 1)
        (PathRhoWords.faceColumn (-PathCoefficientRing.g) PathCoefficientRing.rho (faceIndex I j) bits) := by
  unfold PathOriginalZWordResidue.residue
  change GradedMilnorWittLaurent.residue R site N D K New (PathOriginalZWordResidue.smooth R hI j hj ha)
    (GradedMilnorWittSheaf.pullback site N D
      (S:=CommRingCat.of Old) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (PathOriginalZSignedFace.coefficientPullback R hI j hj ha).toRingHom _) = _
  rw [PathOriginalZWordResidue.pullback_eq]
  exact PathOrderedFaceResidue.full_word R Base hI a 1 j hj ha (j/2) site N D K
    (PathOriginalZWordResidue.smooth R hI j hj ha) P bits hb

theorem z_word_scalar (bits : List Bool) (hb : bits.length=(available I (n+2)).card)
    (c : D.Total (CommRingCat.of R)) :
    PathOriginalZWordResidue.residue R hI j hj ha site N D K
      (wordValue DO (units Base hI a 1) bits * GradedMilnorWittScalarNaturality.scalar R Old site N D c)=
      ((DN).g^(j/2) * evaluate DN (units Base hJ a 1)
        (PathRhoWords.faceColumn (-PathCoefficientRing.g) PathCoefficientRing.rho (faceIndex I j) bits)) *
          GradedMilnorWittScalarNaturality.scalar R New site N D c := by
  have he := z_word R hI j hj ha site N D K P bits hb
  unfold PathOriginalZWordResidue.residue at he ⊢
  change GradedMilnorWittLaurent.residue R site N D K New (PathOriginalZWordResidue.smooth R hI j hj ha)
    (GradedMilnorWittSheaf.pullback site N D
      (S:=CommRingCat.of Old) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (PathOriginalZSignedFace.coefficientPullback R hI j hj ha).toRingHom (_ * _)) = _
  rw [map_mul,GradedMilnorWittScalarNaturality.naturality R Old (LaurentBasepoint.Laurent New) site N D
    (PathOriginalZSignedFace.coefficientPullback R hI j hj ha),
    GradedMilnorWittResidueScalar.coefficient_mul R New site N D K
      (PathOriginalZWordResidue.smooth R hI j hj ha) P]
  exact congrArg (fun x => x * GradedMilnorWittScalarNaturality.scalar R New site N D c) he
end Z

#print axioms y_word
#print axioms y_word_scalar
#print axioms z_word
#print axioms z_word_scalar
end Verification.PathOriginalFullWordResidue
