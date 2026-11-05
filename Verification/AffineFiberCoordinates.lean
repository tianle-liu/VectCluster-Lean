/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine Fiber Coordinates

Explicit affine coordinates on a linear fiber, with affine encoding and
affine decoding defined on the full ambient spaces. These allow actual
sign-label face maps to be composed without assuming affine compatibility.
-/
noncomputable section
namespace Verification.AffineFiberCoordinates
variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [Module.Finite K M]

def retract (L : M →ₗ[K] N) : M →ₗ[K] LinearMap.ker L :=
  (LinearMap.ker L).linearProjOfIsCompl (Submodule.exists_isCompl (LinearMap.ker L)).choose
    (Submodule.exists_isCompl (LinearMap.ker L)).choose_spec

omit [Module.Finite K M] in
theorem retract_apply (L : M →ₗ[K] N) (x : LinearMap.ker L) : retract L x=x :=
  Submodule.linearProjOfIsCompl_apply_left _ _

def basisCoordinates (L : M →ₗ[K] N) :
    LinearMap.ker L ≃ₗ[K] (Fin (Module.finrank K (LinearMap.ker L)) → K) :=
  (Module.finBasis K (LinearMap.ker L)).equivFun

def encode (L : M →ₗ[K] N) (p : M) :
    (Fin (Module.finrank K (LinearMap.ker L)) → K) →ᵃ[K] M :=
  ((LinearMap.ker L).subtype.comp (basisCoordinates L).symm.toLinearMap).toAffineMap +
    AffineMap.const K _ p

def decode (L : M →ₗ[K] N) (p : M) :
    M →ᵃ[K] (Fin (Module.finrank K (LinearMap.ker L)) → K) :=
  ((basisCoordinates L).toLinearMap.comp (retract L)).toAffineMap -
    AffineMap.const K _ (basisCoordinates L (retract L p))

theorem encode_apply (L : M →ₗ[K] N) (p : M)
    (x : Fin (Module.finrank K (LinearMap.ker L)) → K) :
    encode L p x=((basisCoordinates L).symm x : M)+p := rfl

theorem decode_apply (L : M →ₗ[K] N) (p x : M) :
    decode L p x=basisCoordinates L (retract L (x-p)) := by
  simp [decode,map_sub]

theorem encode_fiber (L : M →ₗ[K] N) (p : M)
    (x : Fin (Module.finrank K (LinearMap.ker L)) → K) :
    L (encode L p x)=L p := by
  rw [encode_apply,map_add]
  have h := ((basisCoordinates L).symm x).property
  change L ((basisCoordinates L).symm x : M)=0 at h
  rw [h,zero_add]

theorem decode_encode (L : M →ₗ[K] N) (p : M)
    (x : Fin (Module.finrank K (LinearMap.ker L)) → K) :
    decode L p (encode L p x)=x := by
  rw [decode_apply,encode_apply,add_sub_cancel_right,retract_apply,
    (basisCoordinates L).apply_symm_apply]

theorem encode_decode (L : M →ₗ[K] N) (p x : M) (hx : L x=L p) :
    encode L p (decode L p x)=x := by
  let y : LinearMap.ker L := ⟨x-p,by simp [LinearMap.mem_ker,map_sub,hx]⟩
  have he : retract L (x-p)=y := retract_apply L y
  rw [encode_apply,decode_apply,he,(basisCoordinates L).symm_apply_apply]
  exact sub_add_cancel x p

def fiberEquiv (L : M →ₗ[K] N) (p : M) :
    {x : M // L x=L p} ≃ (Fin (Module.finrank K (LinearMap.ker L)) → K) where
  toFun x := decode L p x.val
  invFun x := ⟨encode L p x,encode_fiber L p x⟩
  left_inv x := Subtype.ext (encode_decode L p x.val x.property)
  right_inv := decode_encode L p

#print axioms retract
#print axioms retract_apply
#print axioms basisCoordinates
#print axioms encode
#print axioms decode
#print axioms encode_apply
#print axioms decode_apply
#print axioms encode_fiber
#print axioms decode_encode
#print axioms encode_decode
#print axioms fiberEquiv
end Verification.AffineFiberCoordinates
