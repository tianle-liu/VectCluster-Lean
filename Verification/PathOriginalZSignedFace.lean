/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalZFrozenFace
import Verification.FinsuppTorusTower
import Verification.PathSignedFaceMap
import Verification.LaurentSignChange

/-!
# Path Original Z Signed Face

The actual Z source map on canonical signed compressed coordinates is
exactly the signed path face, followed by its explicit original-normal sign.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace Verification.PathOriginalZSignedFace
open Verification.PathCompression Verification.PathLiteralStratum Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathCoefficientProjection
open Verification.PathOriginalStratumTransport Verification.PathOriginalFaceIndex
open Verification.PathSignedFaceUnits Verification.PathOriginalZFaceCoordinates
open Verification.PathPresentation Verification.OriginalTorus Verification.FinsuppTorusUniversal
open Verification.PathOriginalZPresentation
open Finset
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (j : ℕ) (hj : j∈Icc 1 n) (ha : Addable I j)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Cnew" => Coefficients (Coefficient R) (nextAdmissible hI j hj ha) (LaurentPolynomialUniversal.parameter R) 1

theorem remaining_position (p : Vertices n I) (hp : p.val≠j) :
    pullback R hI j hj ha (position (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (vertexPosition p))=
      algebraMap Cnew (LaurentBasepoint.Laurent Cnew)
        (PathCoefficientProjection.projection hJ (Coefficient R) (LaurentPolynomialUniversal.parameter R) 1
          (position (Coefficient R) hJ (LaurentPolynomialUniversal.parameter R) 1 (vertexPosition (remainingVertex j p hp)))) := by
  by_cases h₀ : p.val=0
  · have h₁ : vertexPosition p=0 := Fin.ext h₀
    have h₂ : vertexPosition (remainingVertex j p hp)=0 := Fin.ext h₀
    rw [h₁,h₂,position_boundary,position_boundary,boundary_zero,boundary_zero]
    rw [PathOriginalZFrozenFace.coefficient,AlgHom.commutes]
    rfl
  by_cases h₁ : p.val=n+1
  · have h₂ : vertexPosition p=Fin.last (n+1) := Fin.ext h₁
    have h₃ : vertexPosition (remainingVertex j p hp)=Fin.last (n+1) := Fin.ext h₁
    rw [h₂,h₃,position_boundary,position_boundary,boundary_last,boundary_last]
    simp only [map_one]
  · have hp' := mem_range.mp (mem_sdiff.mp p.property).1
    let i : Fin n := ⟨p.val-1,by omega⟩
    have h₂ : vertexPosition p=i.castSucc.succ := by apply Fin.ext;dsimp [vertexPosition,i];omega
    have h₃ : vertexPosition (remainingVertex j p hp)=i.castSucc.succ := by
      apply Fin.ext
      dsimp [vertexPosition,remainingVertex,i]
      omega
    have hi : i∉mutableSet n (insert j I) := by
      rw [mem_mutableSet]
      have hn := (mem_sdiff.mp p.property).2
      change ¬p.val-1+1∈insert j I
      rw [show p.val-1+1=p.val by omega]
      exact fun hh => (mem_insert.mp hh).elim hp hn
    rw [h₂,h₃,position_middle,position_middle,remaining_x R hI j hj ha i hi]

theorem remaining_signed (p : Vertices n I) (hp : p.val≠j) :
    pullback R hI j hj ha (signedUnit (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 p : Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)=
      algebraMap Cnew (LaurentBasepoint.Laurent Cnew)
        (signedCoordinate (Coefficient R) hJ (LaurentPolynomialUniversal.parameter R) 1 (remainingVertex j p hp) : Cnew) := by
  rw [← PathCoefficientProjection.projection_signed hJ (Coefficient R) (LaurentPolynomialUniversal.parameter R) 1 (remainingVertex j p hp),
    signedUnit_val,signedUnit_val,map_mul,map_pow,map_neg,map_one,remaining_position,
    map_mul,map_pow,map_neg,map_one,map_mul,map_pow,map_neg,map_one]
  rfl

theorem normal_signed : pullback R hI j hj ha
    (signedUnit (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (normalVertex j hj ha) : Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)=
      (-1)^(j/2)*LaurentPolynomialUniversal.parameter Cnew := by
  rw [signedUnit_val,map_mul,map_pow,map_neg,map_one]
  have hp : vertexPosition (normalVertex j hj ha)=(normal j hj).castSucc.succ := by
    apply Fin.ext
    exact (normal_position j hj).symm
  rw [hp,position_middle,normal_x]
  rfl

def coefficientPullback : Coefficients (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 →ₐ[R] LaurentBasepoint.Laurent Cnew :=
  (pullback R hI j hj ha).comp ((toLayer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1).restrictScalars R)

theorem signed (p : Vertices n I) :
    coefficientPullback R hI j hj ha (signedCoordinate (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 p : Coefficients (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)=
      LaurentSignChange.map R Cnew (j/2)
        (PathSignedFaceMap.coefficientMap (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha
          (signedCoordinate (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 p : Coefficients (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)) := by
  change pullback R hI j hj ha (toLayer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 _)=_
  rw [toLayer_signed]
  by_cases hp : p.val=j
  · have he : p=normalVertex j hj ha := Subtype.ext hp
    rw [he,normal_signed,PathSignedFaceMap.map_normal,LaurentSignChange.parameter]
  · rw [remaining_signed R hI j hj ha p hp,PathSignedFaceMap.map_remaining (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha p hp,
      LaurentSignChange.coefficient]

theorem coefficientPullback_eq : coefficientPullback R hI j hj ha=
    (LaurentSignChange.map R Cnew (j/2)).comp ((PathSignedFaceMap.coefficientMap (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha).restrictScalars R) := by
  apply Ideal.Quotient.algHom_ext
  apply FinsuppTorusTower.hom_ext R (Coefficient R) (Representatives n I)
  · intro s
    change pullback R hI j hj ha
      (toLayer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1
        (algebraMap (Coefficient R) (Coefficients (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1) s))=
      LaurentSignChange.map R Cnew (j/2)
        (PathSignedFaceMap.coefficientMap (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 j hj ha
          (algebraMap (Coefficient R) (Coefficients (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1) s))
    rw [AlgHom.commutes,PathOriginalZFrozenFace.coefficient,AlgHom.commutes]
    exact (LaurentSignChange.coefficient R Cnew (j/2) (algebraMap (Coefficient R) Cnew s)).symm
  · intro p
    have hp : (signedCoordinate (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (includeRepresentative p) : Coefficients (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)=
        Ideal.Quotient.mk (endpointIdeal (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1) (torusCoordinate (Coefficient R) _ p) := by
      change Ideal.Quotient.mk _ (torusCoordinate (Coefficient R) _ (compress hI (includeRepresentative p)))=_
      rw [compress_include]
    have hh := signed R hI j hj ha (includeRepresentative p)
    rw [hp] at hh
    exact hh
#print axioms remaining_position
#print axioms remaining_signed
#print axioms normal_signed
#print axioms coefficientPullback
#print axioms signed
#print axioms coefficientPullback_eq
end Verification.PathOriginalZSignedFace
