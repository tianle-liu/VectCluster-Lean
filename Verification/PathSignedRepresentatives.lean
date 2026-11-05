/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualFirstCokernel
import Verification.PathMatrixCoefficientGrading

/-!
# Path Signed Representatives

Explicit homogeneous representatives of every original first-boundary
survivor. In particular the weights are computed, not supplied as basis data.
-/

namespace Verification.PathSignedRepresentatives

open Verification.PathWords Verification.PathCokernel Verification.PathSignNormalization
  Verification.PathSignedCokernel Verification.PathActualFirstCokernel

variable {R : Type*} [CommRing R]

noncomputable def representativeVector (g : R) (hg : g*g=1) {m : Bool} {n : ℕ}
    (k : Weight m n) : Word n →₀ R :=
  (wordEquiv g hg n).symm (Finsupp.single (representative k) 1)

theorem representativeVector_single (g : R) (hg : g*g=1) {m : Bool} {n : ℕ}
    (k : Weight m n) : representativeVector g hg k=
      Finsupp.single (representative k) (wordScale g n (representative k)) := by
  change diagonal (wordScale g n) (Finsupp.single (representative k) 1)=_
  rw [diagonal_single,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem representative_count {m : Bool} {n : ℕ} (k : Weight m n) :
    (representative k).val.count true=k.val.val := by
  exact congrArg (fun k : Weight m n => k.val.val) (representative_weight k)

theorem signed_basis_representative (g : R) (hg : g*g=1) (m : Bool) (n : ℕ)
    (heven : m=true → n%2=0) (k : Weight m n) :
    signedWeightBasis g hg m n heven k=
      (LinearMap.range (signedBoundary g m n)).mkQ (representativeVector g hg k) := by
  apply (signedCokernelEquiv g hg m n heven).injective
  simp only [signedWeightBasis,Basis.map_apply,Finsupp.coe_basisSingleOne,
    LinearEquiv.apply_symm_apply,signedCokernelEquiv_mk,representativeVector,
    projection_single,projectionColumn,dif_pos (representative_good k),representative_weight]

noncomputable def zBasis (g : R) (hg : g*g=1) (n : ℕ) :
    Basis (Weight false (n+1)) R (ZCokernel g n) :=
  Finsupp.basisSingleOne.map (zWeightEquiv g hg n).symm

noncomputable def yBasis (g : R) (hg : g*g=1) (a : ℕ) :
    Basis (Weight true (2*a)) R (YCokernel g a) :=
  Finsupp.basisSingleOne.map (yWeightEquiv g hg a).symm

theorem zBasis_representative (g : R) (hg : g*g=1) (n : ℕ) (k : Weight false (n+1)) :
    zBasis g hg n k=(LinearMap.range (Verification.PathFirstBoundaryCutout.zBoundary g n)).mkQ
      (representativeVector g hg k) := by
  apply (zWeightEquiv g hg n).injective
  change (zWeightEquiv g hg n) ((zWeightEquiv g hg n).symm (Finsupp.single k 1))=_
  rw [LinearEquiv.apply_symm_apply]
  change Finsupp.single k 1=projection false (n+1) (wordEquiv g hg (n+1) (representativeVector g hg k))
  simp only [representativeVector,LinearEquiv.apply_symm_apply,projection_single,
    projectionColumn,dif_pos (representative_good k),representative_weight]

theorem yBasis_representative (g : R) (hg : g*g=1) (a : ℕ) (k : Weight true (2*a)) :
    yBasis g hg a k=(LinearMap.range (Verification.PathFirstBoundaryCutout.yBoundary g a)).mkQ
      (representativeVector g hg k) := by
  apply (yWeightEquiv g hg a).injective
  change (yWeightEquiv g hg a) ((yWeightEquiv g hg a).symm (Finsupp.single k 1))=_
  rw [LinearEquiv.apply_symm_apply]
  change Finsupp.single k 1=projection true (2*a) (wordEquiv g hg (2*a) (representativeVector g hg k))
  simp only [representativeVector,LinearEquiv.apply_symm_apply,projection_single,
    projectionColumn,dif_pos (representative_good k),representative_weight]

theorem scale_degree {n : ℕ} (w : Word n) :
    Verification.PathCoefficientGrading.Homogeneous 0
      (wordScale Verification.PathCoefficientRing.g n w) := by
  unfold wordScale
  simpa using Verification.PathMatrixCoefficientGrading.power _ 0
    Verification.PathCoefficientGrading.homogeneous_g (indexSum 0 w.val/2)

#print axioms representativeVector
#print axioms representativeVector_single
#print axioms representative_count
#print axioms signed_basis_representative
#print axioms zBasis
#print axioms yBasis
#print axioms zBasis_representative
#print axioms yBasis_representative
#print axioms scale_degree

end Verification.PathSignedRepresentatives
