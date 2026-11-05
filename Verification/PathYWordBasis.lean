/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TorusModelWordBasis
import Verification.PathOriginalYCoefficient
import Verification.PathEvenEndpointTorus
import Verification.PathClassOrdering

/-!
# Path Y Word Basis

Ordered word coordinates on the genuine Y stratum coefficient fiber.
Every Laurent generator is the actual signed original path coordinate.
-/
noncomputable section
namespace Verification.PathYWordBasis
open Classical CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.OriginalTorus
variable (R : Type) [CommRing R] {a : ℕ} {I : Finset ℕ} (hI : Admissible (2*a) I)
local notation "μ" => PathEvenEndpointTorus.FreeCoordinates hI
local notation "S" => PathOriginalCoefficientTransport.Fiber (I:=I) R Empty (PathOriginalYPresentation.matrix (2*a))

def torusEquiv : S ≃ₐ[R] Torus R μ :=
  (PathOriginalYCoefficient.coefficientEquiv R hI).symm.trans
    (PathEvenEndpointTorus.coefficientEquiv hI R)

def freeUnit (p : μ) : Sˣ :=
  Units.map (PathOriginalYCoefficient.coefficientEquiv R hI).toRingHom.toMonoidHom
    (signedCoordinate R hI 1 1 (includeRepresentative p.val))

theorem map_freeUnit (p : μ) : Units.map (torusEquiv R hI).toRingHom.toMonoidHom (freeUnit R hI p)=
    FinsuppTorusUniversal.unit R μ p := by
  apply Units.ext
  change PathEvenEndpointTorus.coefficientEquiv hI R
    ((PathOriginalYCoefficient.coefficientEquiv R hI).symm
      (PathOriginalYCoefficient.coefficientEquiv R hI
        (signedCoordinate R hI 1 1 (includeRepresentative p.val) : Coefficients R hI 1 1)))=_
  rw [AlgEquiv.symm_apply_apply]
  change PathEvenEndpointTorus.coefficientEquiv hI R
    (Ideal.Quotient.mk (endpointIdeal R hI 1 1) (torusCoordinate R _ (compress hI (includeRepresentative p.val))))=_
  rw [compress_include,PathEvenEndpointTorus.coefficient_coordinate]
  rfl

theorem inverse_unit (p : μ) : Units.map (torusEquiv R hI).symm.toRingHom.toMonoidHom
    (FinsuppTorusUniversal.unit R μ p)=freeUnit R hI p := by
  apply Units.ext
  apply (torusEquiv R hI).injective
  change torusEquiv R hI ((torusEquiv R hI).symm (torusCoordinate R μ p))=_
  rw [AlgEquiv.apply_symm_apply]
  exact (congrArg Units.val (map_freeUnit R hI p)).symm

theorem ordered_unit (i : Fin (Fintype.card μ)) :
    TorusModelWordBasis.unit R S μ (torusEquiv R hI) i=
      freeUnit R hI (TorusModelWordBasis.ordering μ i) := inverse_unit R hI _

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)

def basis : (BinaryWordCoordinates.Index (Fintype.card μ) → D.Total (CommRingCat.of R)) ≃+
    D.Total (CommRingCat.of S) := TorusModelWordBasis.basis R S μ (torusEquiv R hI) site N D K

def word (i : BinaryWordCoordinates.Index (Fintype.card μ)) : D.Total (CommRingCat.of S) :=
  OrderedBinaryWords.word (Fintype.card μ)
    (fun k => (D.symbols (CommRingCat.of S)).symbol
      (freeUnit R hI (TorusModelWordBasis.ordering μ k))) i

theorem model_word (i : BinaryWordCoordinates.Index (Fintype.card μ)) :
    TorusModelWordBasis.word R S μ (torusEquiv R hI) site N D i=word R hI site N D i := by
  unfold TorusModelWordBasis.word word
  congr 1
  funext k
  rw [ordered_unit]

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem basis_single (i : BinaryWordCoordinates.Index (Fintype.card μ)) (c : D.Total (CommRingCat.of R)) :
    basis R hI site N D K (Pi.single i c)=word R hI site N D i*
      GradedMilnorWittScalarNaturality.scalar R S site N D c := by
  rw [basis,TorusModelWordBasis.basis_single R S μ (torusEquiv R hI) site N D K P,model_word]

theorem basis_expansion (c : BinaryWordCoordinates.Index (Fintype.card μ) → D.Total (CommRingCat.of R)) :
    basis R hI site N D K c=∑ i,word R hI site N D i*
      GradedMilnorWittScalarNaturality.scalar R S site N D (c i) := by
  rw [basis,TorusModelWordBasis.basis_expansion R S μ (torusEquiv R hI) site N D K P]
  apply Finset.sum_congr rfl
  intro i _
  rw [model_word]

#print axioms torusEquiv
#print axioms freeUnit
#print axioms map_freeUnit
#print axioms inverse_unit
#print axioms ordered_unit
#print axioms basis
#print axioms word
#print axioms model_word
#print axioms basis_single
#print axioms basis_expansion
end Verification.PathYWordBasis
