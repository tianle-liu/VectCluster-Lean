/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualResidueMatrix

/-!
# Path Actual Normal Word Faces

Reindex the computed actual residue by the literal normal words used
in the original path matrix, preserving the same finite section vectors.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathActualNormalWordFaces
open Classical CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedFaceUnits
open Verification.PathActualWordIndices Verification.PathMilnorWittCoefficients
open Verification.PathActualResidueCoordinates Verification.PathNormalizedBasis Verification.PathEndpointWords

def reindex {ι κ ι' κ' A : Type*} [AddCommGroup A] (e : ι ≃ ι') (d : κ ≃ κ')
    (F : (ι → A) →+ (κ → A)) : (ι' → A) →+ (κ' → A) where
  toFun f k := F (fun i => f (e i)) (d.symm k)
  map_zero' := by funext k;exact congrFun F.map_zero (d.symm k)
  map_add' f g := by funext k;exact congrFun (F.map_add (fun i => f (e i)) (fun i => g (e i))) (d.symm k)

section Y
variable (R : Type) [CommRing R] {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
local notation "SI" => NormalWord BothNormal (available I (2*d+2)).card
local notation "TI" => NormalWord BothNormal (available (insert j I) (2*d+2)).card
local notation "DR" => D.symbols (CommRingCat.of R)

def yFace : (SI → D.Total (CommRingCat.of R)) →+ (TI → D.Total (CommRingCat.of R)) :=
  reindex (yWordEquiv hI) (yWordEquiv (nextAdmissible hI j hj ha))
    (PathActualResidueCoordinates.yFace R hI j hj ha site N D K)

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem y_apply (f : SI → D.Total (CommRingCat.of R)) (k : TI) :
    yFace R hI j hj ha site N D K f k=
      ∑ i:SI,((DR).g^(j/2)*realize (DR).toCoefficients
        ((PathLeftEndpoint.projection 0 (PathLiteralEntries.projectedFace PathCoefficientRing.g PathCoefficientRing.rho (2*d) (faceIndex I j) i.val)) k.val))*f i := by
  change PathActualResidueCoordinates.yFace R hI j hj ha site N D K
    (fun i => f (yWordEquiv hI i)) ((yWordEquiv (nextAdmissible hI j hj ha)).symm k)=_
  rw [PathActualResidueMatrix.y_apply R hI j hj ha site N D K P]
  simp only [Equiv.apply_symm_apply]
  exact Fintype.sum_equiv (yWordEquiv hI) _ _ (fun i => rfl)
end Y

section Z
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible (n) I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (n)) (ha : Addable I j)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
local notation "SI" => NormalWord RightNormal (available I (n+2)).card
local notation "TI" => NormalWord RightNormal (available (insert j I) (n+2)).card
local notation "DR" => D.symbols (CommRingCat.of R)

def zFace : (SI → D.Total (CommRingCat.of R)) →+ (TI → D.Total (CommRingCat.of R)) :=
  reindex (zWordEquiv hI) (zWordEquiv (nextAdmissible hI j hj ha))
    (PathActualResidueCoordinates.zFace R hI j hj ha site N D K)

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem z_apply (f : SI → D.Total (CommRingCat.of R)) (k : TI) :
    zFace R hI j hj ha site N D K f k=
      ∑ i:SI,((DR).g^(j/2)*realize (DR).toCoefficients
        ((PathLiteralEntries.projectedFace PathCoefficientRing.g PathCoefficientRing.rho (n) (faceIndex I j) i.val) k.val))*f i := by
  change PathActualResidueCoordinates.zFace R hI j hj ha site N D K
    (fun i => f (zWordEquiv hI i)) ((zWordEquiv (nextAdmissible hI j hj ha)).symm k)=_
  rw [PathActualResidueMatrix.z_apply R hI j hj ha site N D K P]
  simp only [Equiv.apply_symm_apply]
  exact Fintype.sum_equiv (zWordEquiv hI) _ _ (fun i => rfl)
end Z

#print axioms reindex
#print axioms yFace
#print axioms y_apply
#print axioms zFace
#print axioms z_apply
end Verification.PathActualNormalWordFaces
