/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalZCoefficient
import Verification.PathOriginalFaceIndex
import Verification.OriginalZeroLayerCast
import Verification.OriginalSourceLaurentGenerators

/-!
# Path Original Z Face Coordinates

The actual original Z adjacent map, transported to path coefficient
coordinates, retains every surviving original coordinate and its literal normal.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace Verification.PathOriginalZFaceCoordinates
open Verification.PathCompression Verification.PathLiteralStratum Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathCoefficientProjection
open Verification.PathOriginalStratumTransport Verification.PathOriginalIndependence
open Verification.PathOriginalZPresentation Verification.PathOriginalFaceIndex
open Verification.PathSignedFaceUnits Verification.IndependentChartIndex
open Verification.IndependentBasicOpen
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "J" => mutableSet n (insert j I)
local notation "v" => selectedNormal (I:=I) j hj
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Cnew" => Coefficients (Coefficient R) (nextAdmissible hI j hj ha) (LaurentPolynomialUniversal.parameter R) 1
local notation "New" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R (Fin 1) (matrix n)
local notation "pos" => positive_order (matrix n) z_mutable
local notation "neg" => negative_order (matrix n) z_mutable
local notation "supp" => support (matrix n) z_mutable
local notation "indep" => independent (matrix n) z_mutable (nextAdmissible hI j hj ha)
local notation "hD" => matrix_zero_block (Fin 1) n J (matrix n) pos neg supp indep

def sourceEquiv : Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 ≃ₐ[R]
    GlobalNormalFrame.ZeroLayer R (Fin 1) n ((J).erase (v).val) (matrix n) :=
  (PathOriginalZStratum.equiv R hI).trans
    (OriginalZeroLayerCast.equiv R (Fin 1) n (matrix n) (mutable_erase j hj ha).symm)

theorem source_x (i : Fin n) : sourceEquiv R hI j hj ha (layerX (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 i)=
    ExplicitStratumCoordinates.original R (Fin 1) n ((J).erase (v).val) (matrix n) (Sum.inl i) := by
  change OriginalZeroLayerCast.equiv R (Fin 1) n (matrix n) (mutable_erase j hj ha).symm
    (PathOriginalZStratum.equiv R hI (layerX (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 i))=_
  rw [PathOriginalZStratum.equiv_x]
  exact OriginalZeroLayerCast.original R (Fin 1) n (matrix n) _ (Sum.inl i)

def pullback : Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 →ₐ[R] LaurentBasepoint.Laurent Cnew :=
  (LaurentSheafBaseChange.laurentMap R New Cnew (PathOriginalZCoefficient.coefficientEquiv R hJ).symm.toAlgHom).comp
    ((OriginalSourceLaurentGenerators.map R (Fin 1) n J (matrix n) v hD).comp
      (sourceEquiv R hI j hj ha).toAlgHom)

theorem normal_x : pullback R hI j hj ha (layerX (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (normal j hj))=
    LaurentPolynomialUniversal.parameter Cnew := by
  change LaurentSheafBaseChange.laurentMap R New Cnew (PathOriginalZCoefficient.coefficientEquiv R hJ).symm.toAlgHom
    (OriginalSourceLaurentGenerators.map R (Fin 1) n J (matrix n) v hD
      (sourceEquiv R hI j hj ha (layerX (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (normal j hj))))=_
  rw [source_x]
  have hp := OriginalSourceLaurentGenerators.parameter R (Fin 1) n J (matrix n) v hD
  change OriginalSourceLaurentGenerators.map R (Fin 1) n J (matrix n) v hD
    (ExplicitStratumCoordinates.original R (Fin 1) n ((J).erase (v).val) (matrix n) (Sum.inl (normal j hj)))=_ at hp
  rw [hp]
  exact LaurentSheafBaseChange.map_parameter R New Cnew _

theorem remaining_x (i : Fin n) (hi : i∉J) :
    pullback R hI j hj ha (layerX (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 i)=
      algebraMap Cnew (LaurentBasepoint.Laurent Cnew)
        (PathCoefficientProjection.projection hJ (Coefficient R) (LaurentPolynomialUniversal.parameter R) 1 (layerX (Coefficient R) hJ (LaurentPolynomialUniversal.parameter R) 1 i)) := by
  let a : AnticliqueSubcolumns.Rows (C:=Fin 1) J := ⟨Sum.inl i,by intro k hk he;exact hi ((Sum.inl.inj he).symm ▸ hk)⟩
  change LaurentSheafBaseChange.laurentMap R New Cnew (PathOriginalZCoefficient.coefficientEquiv R hJ).symm.toAlgHom
    (OriginalSourceLaurentGenerators.map R (Fin 1) n J (matrix n) v hD
      (sourceEquiv R hI j hj ha (layerX (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 i)))=_
  rw [source_x]
  have hh := OriginalSourceLaurentGenerators.remaining R (Fin 1) n J (matrix n) v hD pos neg supp indep a
  change OriginalSourceLaurentGenerators.map R (Fin 1) n J (matrix n) v hD
    (ExplicitStratumCoordinates.original R (Fin 1) n ((J).erase (v).val) (matrix n) (Sum.inl i))=_ at hh
  rw [hh,LaurentSheafBaseChange.map_coefficient]
  have hp := PathOriginalZCoefficient.projection R hJ (layerX (Coefficient R) hJ (LaurentPolynomialUniversal.parameter R) 1 i)
  rw [PathOriginalZStratum.equiv_x] at hp
  change PathOriginalZCoefficient.coefficientEquiv R hJ
    (PathCoefficientProjection.projection hJ (Coefficient R) (LaurentPolynomialUniversal.parameter R) 1 (layerX (Coefficient R) hJ (LaurentPolynomialUniversal.parameter R) 1 i))=
    OriginalCanonicalFiberProjection.projection R (Fin 1) n J (matrix n) pos neg supp indep
      (ExplicitStratumCoordinates.original R (Fin 1) n J (matrix n) (Sum.inl i)) at hp
  rw [← hp]
  exact congrArg (algebraMap Cnew (LaurentBasepoint.Laurent Cnew))
    ((PathOriginalZCoefficient.coefficientEquiv R hJ).symm_apply_apply _)

#print axioms sourceEquiv
#print axioms source_x
#print axioms pullback
#print axioms normal_x
#print axioms remaining_x
end Verification.PathOriginalZFaceCoordinates
