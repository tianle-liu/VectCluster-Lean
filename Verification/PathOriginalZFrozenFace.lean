/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalZFaceCoordinates

/-!
# Path Original Z Frozen Face

The true Z adjacent map preserves the freely variable frozen endpoint
as a coefficient, even when its compressed endpoint classes coincide.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace Verification.PathOriginalZFrozenFace
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

open Verification.PathOriginalZFaceCoordinates

theorem source_parameter : sourceEquiv R hI j hj ha
    (algebraMap (Coefficient R) (Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)
      (LaurentPolynomialUniversal.parameter R))=
    ExplicitStratumCoordinates.original R (Fin 1) n ((J).erase (v).val) (matrix n) (Sum.inr 0) := by
  change OriginalZeroLayerCast.equiv R (Fin 1) n (matrix n) (mutable_erase j hj ha).symm
    (PathOriginalZStratum.equiv R hI
      (algebraMap (Coefficient R) (Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)
        (LaurentPolynomialUniversal.parameter R)))=_
  rw [PathOriginalZStratum.equiv_parameter]
  exact OriginalZeroLayerCast.original R (Fin 1) n (matrix n) _ (Sum.inr 0)

theorem frozen : pullback R hI j hj ha
    (algebraMap (Coefficient R) (Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)
      (LaurentPolynomialUniversal.parameter R))=
      algebraMap (Coefficient R) (LaurentBasepoint.Laurent Cnew) (LaurentPolynomialUniversal.parameter R) := by
  let a : AnticliqueSubcolumns.Rows (C:=Fin 1) J := ⟨Sum.inr 0,by intros;exact Sum.inr_ne_inl⟩
  change LaurentSheafBaseChange.laurentMap R New Cnew (PathOriginalZCoefficient.coefficientEquiv R hJ).symm.toAlgHom
    (OriginalSourceLaurentGenerators.map R (Fin 1) n J (matrix n) v hD
      (sourceEquiv R hI j hj ha
        (algebraMap (Coefficient R) (Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)
          (LaurentPolynomialUniversal.parameter R))))=_
  rw [source_parameter]
  have hh := OriginalSourceLaurentGenerators.remaining R (Fin 1) n J (matrix n) v hD pos neg supp indep a
  change OriginalSourceLaurentGenerators.map R (Fin 1) n J (matrix n) v hD
    (ExplicitStratumCoordinates.original R (Fin 1) n ((J).erase (v).val) (matrix n) (Sum.inr 0))=_ at hh
  rw [hh,LaurentSheafBaseChange.map_coefficient]
  have hp := PathOriginalZCoefficient.projection R hJ
    (algebraMap (Coefficient R) (Layer (Coefficient R) hJ (LaurentPolynomialUniversal.parameter R) 1)
      (LaurentPolynomialUniversal.parameter R))
  rw [PathOriginalZStratum.equiv_parameter,AlgHom.commutes] at hp
  change PathOriginalZCoefficient.coefficientEquiv R hJ
    (algebraMap (Coefficient R) Cnew (LaurentPolynomialUniversal.parameter R))=
    OriginalCanonicalFiberProjection.projection R (Fin 1) n J (matrix n) pos neg supp indep
      (ExplicitStratumCoordinates.original R (Fin 1) n J (matrix n) (Sum.inr 0)) at hp
  rw [← hp]
  change algebraMap Cnew (LaurentBasepoint.Laurent Cnew)
    ((PathOriginalZCoefficient.coefficientEquiv R hJ).symm
      ((PathOriginalZCoefficient.coefficientEquiv R hJ) _))=_
  rw [AlgEquiv.symm_apply_apply]
  rfl

theorem coefficient (s : Coefficient R) : pullback R hI j hj ha
    (algebraMap (Coefficient R) (Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1) s)=
      algebraMap (Coefficient R) (LaurentBasepoint.Laurent Cnew) s := by
  have hh : (pullback R hI j hj ha).comp
      (IsScalarTower.toAlgHom R (Coefficient R) (Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1))=
      IsScalarTower.toAlgHom R (Coefficient R) (LaurentBasepoint.Laurent Cnew) := by
    apply LaurentPolynomialUniversal.hom_ext
    · intro r
      rw [AlgHom.commutes,AlgHom.commutes]
    · exact frozen R hI j hj ha
  exact AlgHom.congr_fun hh s

#print axioms source_parameter
#print axioms frozen
#print axioms coefficient
end Verification.PathOriginalZFrozenFace
