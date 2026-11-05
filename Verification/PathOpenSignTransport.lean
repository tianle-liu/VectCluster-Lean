/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenSignedQuotient
import Verification.PathProjectedTwist
import Verification.PathSignQuotients

/-!
# Path Open Sign Transport

Full affine endpoint normalization and independent phase compensation for
open recursion. The ring and rho differential remain unspecialized.
-/

namespace Verification.PathOpenSignTransport

open Classical Verification.PathCochains Verification.PathRhoFinite Verification.PathRhoFaces
  Verification.PathRhoSeparated Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathEndpointTotal Verification.PathEndpointComplex Verification.PathProjectedTwist
  Verification.PathClosedSignedComplex Verification.PathClosedEndpointTransport
  Verification.PathOpenSignedQuotient Verification.PathSignQuotients

variable {R : Type*} [CommRing R]

section Generic
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem symm_intertwining (e : M ≃ₗ[R] N) (D : M →ₗ[R] M) (E : N →ₗ[R] N)
    (h : E.comp e.toLinearMap=e.toLinearMap.comp D) :
    D.comp e.symm.toLinearMap=e.symm.toLinearMap.comp E := by
  apply LinearMap.ext
  intro x
  apply e.injective
  have hh := LinearMap.congr_fun h (e.symm x)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using hh.symm
end Generic

theorem projected_scalar_twist (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
    (hP : ∀ n x, x ∈ layer (R := R) n → P x ∈ layer n)
    (g ρ u : R) (hu : u*u=1) (n : ℕ) :
    (imageDifferential (totalMap P hP n) (differential g ρ n)).comp (projectedTwist P hP u n)=
      u • (projectedTwist P hP u n).comp
        (imageDifferential (totalMap P hP n) (differential g ρ n)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change totalMap P hP n (differential g ρ n (degreeTwist u n x.val))=
    u • degreeTwist u n (totalMap P hP n (differential g ρ n x.val))
  have hd := LinearMap.congr_fun (differential_scalar_twist g ρ u hu n) x.val
  simp only [LinearMap.comp_apply,LinearMap.smul_apply] at hd
  rw [hd,map_smul]
  congr 1
  exact LinearMap.congr_fun (totalMap_twist P hP u n) (differential g ρ n x.val)

noncomputable def rightTwist (g : R) (hg : g*g=1) (k : R) (n : ℕ) (bit : Bool) :
    LinearMap.range (right k n) ≃ₗ[R] LinearMap.range (right k n) :=
  projectedTwistEquiv (Verification.PathRightEndpoint.projection k)
    (Verification.PathRightEndpoint.projection_mem_layer k) (phase (-g) bit)
    (phase_squared (-g) (by simpa only [neg_mul_neg] using hg) bit) n

/-- This goes from the literal old endpoint constant to its shorter normalized constant. -/
noncomputable def normalizedEquiv (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (bit : Bool) :
    LinearMap.range (right k n) ≃ₗ[R]
      LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n) :=
  (rightTwist g hg k n bit).trans (rightSignEquiv g ρ hg hr a b k n).symm

theorem normalized_intertwining (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (bit : Bool) (hk : k*k=ρ*k) :
    (imageDifferential (right (flipConstant g ρ (signAt a b (n+1)) k) n) (differential g ρ n)).comp
        (normalizedEquiv g ρ hg hr a b k n bit).toLinearMap=
      (normalizedEquiv g ρ hg hr a b k n bit).toLinearMap.comp
        (phase (-g) bit • imageDifferential (right k n) (differential g ρ n)) := by
  apply LinearMap.ext
  intro x
  have hs := LinearMap.congr_fun (symm_intertwining (R := R)
    (M := LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
    (N := LinearMap.range (right k n))
    (rightSignEquiv g ρ hg hr a b k n)
    (imageDifferential (right (flipConstant g ρ (signAt a b (n+1)) k) n) (differential g ρ n))
    (imageDifferential (right k n) (differential g ρ n))
    (rightSign_differential g ρ hg hr a b k n hk)) (rightTwist g hg k n bit x)
  have ht := LinearMap.congr_fun (projected_scalar_twist
    (Verification.PathRightEndpoint.projection k) (Verification.PathRightEndpoint.projection_mem_layer k)
    g ρ (phase (-g) bit) (phase_squared (-g) (by simpa only [neg_mul_neg] using hg) bit) n) x
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,LinearEquiv.coe_coe] at hs ht
  change imageDifferential (right k n) (differential g ρ n) (rightTwist g hg k n bit x)=
    phase (-g) bit • rightTwist g hg k n bit (imageDifferential (right k n) (differential g ρ n) x) at ht
  change imageDifferential _ _ ((rightSignEquiv g ρ hg hr a b k n).symm (rightTwist g hg k n bit x))=
    (rightSignEquiv g ρ hg hr a b k n).symm
      (rightTwist g hg k n bit (phase (-g) bit • imageDifferential (right k n) (differential g ρ n) x))
  rw [hs,ht]
  simp only [map_smul]

#print axioms symm_intertwining
#print axioms projected_scalar_twist
#print axioms rightTwist
#print axioms normalizedEquiv
#print axioms normalized_intertwining

end Verification.PathOpenSignTransport
