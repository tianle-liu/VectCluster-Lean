/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOrderedWordValues
import Verification.PathOrderedCoordinateList
import Verification.PathActualWordIndices
import Verification.PathYWordBasis
import Verification.PathZWordBasis

/-!
# Path Actual Ordered Word Comparison

Genuine Y/Z torus basis words pull back to the literal sorted word
evaluation used by the full Milnor-Witt path face. No endpoint symbol is
discarded except through its normal false bit.
-/
noncomputable section
namespace Verification.PathActualOrderedWordComparison
open Classical CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathOrderedFaceUnits
open Verification.PathOrderedCoordinateList Verification.PathFreeCoordinateOrder
open Verification.PathMilnorWittWordFace Verification.PathActualWordIndices
open Verification.GradedMilnorWittSheaf Verification.BinaryWordCoordinates
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : Standard site N)

theorem z_word {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (i : Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))) :
    pullback site N D (PathOriginalZCoefficient.coefficientEquiv R hI).symm.toRingHom
      (PathZWordBasis.word R hI site N D i)=
    wordValue (D.symbols (CommRingCat.of (Coefficients (LaurentPolynomialUniversal.Laurent R) hI
      (LaurentPolynomialUniversal.parameter R) 1)))
      (units (LaurentPolynomialUniversal.Laurent R) hI (LaurentPolynomialUniversal.parameter R) 1)
      (zWordEquiv hI i).val := by
  rw [zWordEquiv_val,PathOrderedWordValues.right_word _ _ _ (by
    rw [length_units];have hh:=z_card hI;omega)]
  unfold PathZWordBasis.word
  rw [PathOrderedWordValues.map_word]
  congr 1
  funext k
  rw [pullback_symbol,z_at]
  congr 1
  apply Units.ext
  change (PathOriginalZCoefficient.coefficientEquiv R hI).symm
    ((PathOriginalZCoefficient.coefficientEquiv R hI) _) = _
  exact AlgEquiv.symm_apply_apply _ _

theorem y_word {a : ℕ} {I : Finset ℕ} (hI : Admissible (2*a) I)
    (i : Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))) :
    pullback site N D (PathOriginalYCoefficient.coefficientEquiv R hI).symm.toRingHom
      (PathYWordBasis.word R hI site N D i)=
    wordValue (D.symbols (CommRingCat.of (Coefficients R hI 1 1)))
      (units R hI 1 1) (yWordEquiv hI i).val := by
  rw [yWordEquiv_val,PathOrderedWordValues.both_word _ _ _ (by
    rw [length_units];have hh:=y_card hI;omega)]
  unfold PathYWordBasis.word
  rw [PathOrderedWordValues.map_word]
  congr 1
  funext k
  rw [pullback_symbol,y_at]
  congr 1
  apply Units.ext
  change (PathOriginalYCoefficient.coefficientEquiv R hI).symm
    ((PathOriginalYCoefficient.coefficientEquiv R hI) _) = _
  exact AlgEquiv.symm_apply_apply _ _

#print axioms z_word
#print axioms y_word
end Verification.PathActualOrderedWordComparison
