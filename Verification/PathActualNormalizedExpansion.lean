/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathNormalizedWordEvaluation
import Verification.PathActualOrderedWordComparison

/-!
# Path Actual Normalized Expansion

The actual finite torus basis reconstructs every normalized formal path
column, with central g/rho weights and arbitrary base sections.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace Verification.PathActualNormalizedExpansion
open Classical CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedStratumCoefficients
open Verification.PathOrderedFaceUnits Verification.PathMilnorWittWordFace
open Verification.PathMilnorWittCoefficients Verification.PathActualWordIndices
open Verification.PathNormalizedBasis Verification.PathEndpointWords

section Y
variable (R : Type) [CommRing R] {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "Base" => R
local notation "a" => (1:R)
local notation "Comp" => Coefficients Base hI a 1
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Empty) (PathOriginalYPresentation.matrix (2*d))
local notation "DR" => D.symbols (CommRingCat.of R)
local notation "DC" => D.symbols (CommRingCat.of Comp)
local notation "len" => (available I (2*d+2)).card
include P

theorem y_expansion (f : List Bool →₀ PathCoefficientRing.Coeff)
    (hf : f∈normalLayer (R:=PathCoefficientRing.Coeff) BothNormal len)
    (w : ℕ) (c : D.Total (CommRingCat.of R)) :
    GradedMilnorWittSheaf.pullback site N D (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Comp)
      (PathOriginalYCoefficient.coefficientEquiv R hI).symm.toRingHom
      (PathYWordBasis.basis R hI site N D K
        (fun i => (DR).g^w * realize (DR).toCoefficients (f (yWordEquiv hI i).val) * c))=
      (DC).g^w * evaluate DC (units Base hI a 1) f * GradedMilnorWittScalarNaturality.scalar R Comp site N D c := by
  have hc (b : D.Total (CommRingCat.of R)) :=
    GradedMilnorWittScalarNaturality.naturality R Fiber Comp site N D
      (PathOriginalYCoefficient.coefficientEquiv R hI).symm.toAlgHom b
  have hc' (b : D.Total (CommRingCat.of R)) :
      GradedMilnorWittSheaf.pullback site N D (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Comp)
        (PathOriginalYCoefficient.coefficientEquiv R hI).symm.toRingHom
        (GradedMilnorWittScalarNaturality.scalar R Fiber site N D b)=
      GradedMilnorWittScalarNaturality.scalar R Comp site N D b := hc b
  have hn := GradedMilnorWittSheaf.compatible site N D
    (S:=CommRingCat.of R) (T:=CommRingCat.of Comp) (algebraMap R Comp)
  have hv := PathNormalizedWordEvaluation.weighted_normal (DR).toCoefficients DC
    (GradedMilnorWittScalarNaturality.scalar R Comp site N D) hn.g hn.rho
    (units Base hI a 1) BothNormal len f hf w c
  calc
    _ = ∑ i:BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)),
        wordValue DC (units Base hI a 1) (yWordEquiv hI i).val *
          GradedMilnorWittScalarNaturality.scalar R Comp site N D
            ((DR).g^w*realize (DR).toCoefficients (f (yWordEquiv hI i).val)*c) := by
      rw [PathYWordBasis.basis_expansion R hI site N D K P,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul,hc',PathActualOrderedWordComparison.y_word R site N D hI i]
    _ = ∑ i:NormalWord BothNormal len,
        wordValue DC (units Base hI a 1) i.val *
          GradedMilnorWittScalarNaturality.scalar R Comp site N D
            ((DR).g^w*realize (DR).toCoefficients (f i.val)*c) := Fintype.sum_equiv (yWordEquiv hI) _ _ (fun i => rfl)
    _ = _ := hv.symm
end Y

section Z
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible (n) I)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "Base" => LaurentBasepoint.Laurent R
local notation "a" => (LaurentPolynomialUniversal.parameter R)
local notation "Comp" => Coefficients Base hI a 1
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) (PathOriginalZPresentation.matrix (n))
local notation "DR" => D.symbols (CommRingCat.of R)
local notation "DC" => D.symbols (CommRingCat.of Comp)
local notation "len" => (available I (n+2)).card
include P

theorem z_expansion (f : List Bool →₀ PathCoefficientRing.Coeff)
    (hf : f∈normalLayer (R:=PathCoefficientRing.Coeff) RightNormal len)
    (w : ℕ) (c : D.Total (CommRingCat.of R)) :
    GradedMilnorWittSheaf.pullback site N D (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Comp)
      (PathOriginalZCoefficient.coefficientEquiv R hI).symm.toRingHom
      (PathZWordBasis.basis R hI site N D K
        (fun i => (DR).g^w * realize (DR).toCoefficients (f (zWordEquiv hI i).val) * c))=
      (DC).g^w * evaluate DC (units Base hI a 1) f * GradedMilnorWittScalarNaturality.scalar R Comp site N D c := by
  have hc (b : D.Total (CommRingCat.of R)) :=
    GradedMilnorWittScalarNaturality.naturality R Fiber Comp site N D
      (PathOriginalZCoefficient.coefficientEquiv R hI).symm.toAlgHom b
  have hc' (b : D.Total (CommRingCat.of R)) :
      GradedMilnorWittSheaf.pullback site N D (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Comp)
        (PathOriginalZCoefficient.coefficientEquiv R hI).symm.toRingHom
        (GradedMilnorWittScalarNaturality.scalar R Fiber site N D b)=
      GradedMilnorWittScalarNaturality.scalar R Comp site N D b := hc b
  have hn := GradedMilnorWittSheaf.compatible site N D
    (S:=CommRingCat.of R) (T:=CommRingCat.of Comp) (algebraMap R Comp)
  have hv := PathNormalizedWordEvaluation.weighted_normal (DR).toCoefficients DC
    (GradedMilnorWittScalarNaturality.scalar R Comp site N D) hn.g hn.rho
    (units Base hI a 1) RightNormal len f hf w c
  calc
    _ = ∑ i:BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)),
        wordValue DC (units Base hI a 1) (zWordEquiv hI i).val *
          GradedMilnorWittScalarNaturality.scalar R Comp site N D
            ((DR).g^w*realize (DR).toCoefficients (f (zWordEquiv hI i).val)*c) := by
      rw [PathZWordBasis.basis_expansion R hI site N D K P,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul,hc',PathActualOrderedWordComparison.z_word R site N D hI i]
    _ = ∑ i:NormalWord RightNormal len,
        wordValue DC (units Base hI a 1) i.val *
          GradedMilnorWittScalarNaturality.scalar R Comp site N D
            ((DR).g^w*realize (DR).toCoefficients (f i.val)*c) := Fintype.sum_equiv (zWordEquiv hI) _ _ (fun i => rfl)
    _ = _ := hv.symm
end Z

#print axioms y_expansion
#print axioms z_expansion
end Verification.PathActualNormalizedExpansion
