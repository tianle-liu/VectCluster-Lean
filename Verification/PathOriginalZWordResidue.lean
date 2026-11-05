/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFaceActualWordResidue
import Verification.PathOriginalZSignedFace
import Verification.PathVariableEndpointTorus
import Verification.TorusSmooth

/-!
# Path Original Z Word Residue

Actual original Z face residues in the full ordered signed word basis.
Smoothness of the coefficient ring follows from its constructed endpoint torus.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathOriginalZWordResidue
open CategoryTheory AlgebraicGeometry Verification.PathOriginalZPresentation
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathSignedFaceUnits
open Verification.PathMilnorWittWordFace Verification.PathFaceActualWordResidue Finset
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (j : ℕ) (hj : j∈Icc 1 n) (ha : Addable I j)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Old" => Coefficients (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1
local notation "New" => Coefficients (Coefficient R) (nextAdmissible hI j hj ha) (LaurentPolynomialUniversal.parameter R) 1

theorem smooth : Algebra.Smooth R New := by
  classical
  letI := TorusSmooth.torus_smooth R (PathVariableEndpointMaps.FreeCoordinates hJ)
  exact Algebra.Smooth.of_equiv (PathVariableEndpointTorus.coefficientEquiv R hJ).symm

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
local notation "DN" => D.symbols (CommRingCat.of New)
local notation "left" => leftVertex (nextAdmissible hI j hj ha) ⟨j,mem_insert_self j I⟩

theorem pullback_eq : GradedMilnorWittSheaf.pullback site N D
    (S:=CommRingCat.of Old) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
    (PathOriginalZSignedFace.coefficientPullback R hI j hj ha).toRingHom =
    PathFaceSheafSymbols.pullback R (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha (j/2) site N D := by
  rw [PathOriginalZSignedFace.coefficientPullback_eq]
  rfl

def residue : D.Total (CommRingCat.of Old) →+ D.Total (CommRingCat.of New) :=
  (GradedMilnorWittLaurent.residue R site N D K New (smooth R hI j hj ha)).comp
    (GradedMilnorWittSheaf.pullback site N D
      (S:=CommRingCat.of Old) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (PathOriginalZSignedFace.coefficientPullback R hI j hj ha).toRingHom).toAddMonoidHom

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem word (xs ys : List (Vertices n (insert j I) × Bool)) (l m t : Bool) :
    residue R hI j hj ha site N D K (sourceWord (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha site N D xs ys l m t)=
      (DN).g^(j/2) * evaluate DN
        ((targetPairs (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha xs).map Prod.fst ++
          signedCoordinate (Coefficient R) hJ (LaurentPolynomialUniversal.parameter R) 1 left :: (targetPairs (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha ys).map Prod.fst)
        (Verification.PathRhoWords.faceColumn (-Verification.PathCoefficientRing.g)
          Verification.PathCoefficientRing.rho ((targetPairs (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha xs).map Prod.snd).length
          ((targetPairs (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha xs).map Prod.snd ++
            l::m::t::(targetPairs (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha ys).map Prod.snd)) := by
  change GradedMilnorWittLaurent.residue R site N D K New (smooth R hI j hj ha)
    (GradedMilnorWittSheaf.pullback site N D
      (S:=CommRingCat.of Old) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (PathOriginalZSignedFace.coefficientPullback R hI j hj ha).toRingHom _) = _
  rw [pullback_eq]
  exact PathFaceActualWordResidue.residue_word R (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha (j/2) site N D K
    (smooth R hI j hj ha) P xs ys l m t

theorem word_scalar (xs ys : List (Vertices n (insert j I) × Bool)) (l m t : Bool)
    (c : D.Total (CommRingCat.of R)) :
    residue R hI j hj ha site N D K (sourceWord (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha site N D xs ys l m t *
      GradedMilnorWittScalarNaturality.scalar R Old site N D c)=
      residue R hI j hj ha site N D K (sourceWord (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha site N D xs ys l m t) *
        GradedMilnorWittScalarNaturality.scalar R New site N D c := by
  unfold residue
  change GradedMilnorWittLaurent.residue R site N D K New (smooth R hI j hj ha)
    (GradedMilnorWittSheaf.pullback site N D
      (S:=CommRingCat.of Old) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (PathOriginalZSignedFace.coefficientPullback R hI j hj ha).toRingHom _) = _
  rw [pullback_eq]
  exact PathFaceActualWordResidue.residue_word_scalar R (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha (j/2) site N D K
    (smooth R hI j hj ha) P xs ys l m t c

#print axioms smooth
#print axioms pullback_eq
#print axioms residue
#print axioms word
#print axioms word_scalar
end Verification.PathOriginalZWordResidue
