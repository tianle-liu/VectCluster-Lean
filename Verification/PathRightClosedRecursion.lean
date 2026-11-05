/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathProjectedTwist

/-!
# Path Right Closed Recursion

Actual right-endpoint quotient recursion on the closed part, including
the full affine sign substitution and every rho differential term.
-/

namespace Verification.PathRightClosedRecursion

open Classical Verification.PathCochains Verification.PathRhoFinite
  Verification.PathEndpointTotal Verification.PathEndpointComplex Verification.PathAffineLeftEndpoint
  Verification.PathAffineRightEndpoint Verification.PathSignQuotients Verification.PathClosedEmbedding
  Verification.PathClosedEndpointTransport Verification.PathProjectedTwist

variable {R : Type*} [CommRing R]

noncomputable def rightExtension (k : R) (n : ℕ) :
    LinearMap.range (right k n) →ₗ[R] LinearMap.range (right k (n+2)) :=
  projectedExtension (Verification.PathRightEndpoint.projection k)
    (Verification.PathRightEndpoint.projection_mem_layer k) n

noncomputable def rightTwist (g : R) (hg : g*g=1) (k : R) (n : ℕ) :
    LinearMap.range (right k n) ≃ₗ[R] LinearMap.range (right k n) :=
  projectedTwistEquiv (Verification.PathRightEndpoint.projection k)
    (Verification.PathRightEndpoint.projection_mem_layer k) g hg n

variable (g ρ : R)

noncomputable def recursionEquiv (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) :
    LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n) ≃ₗ[R]
      LinearMap.range (right k n) :=
  (rightSignEquiv g ρ hg hr a b k n).trans (rightTwist g hg k n)

noncomputable def closedMap (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) :
    LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n) →ₗ[R]
      LinearMap.range (right k (n+2)) :=
  (rightExtension k n).comp (recursionEquiv g ρ hg hr a b k n).toLinearMap

theorem closedMap_injective (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) : Function.Injective (closedMap g ρ hg hr a b k n) :=
  (projectedExtension_injective (Verification.PathRightEndpoint.projection k)
    (Verification.PathRightEndpoint.projection_mem_layer k) n).comp
      (recursionEquiv g ρ hg hr a b k n).injective

/-- Its range is precisely all original closed strata after imposing the right constant. -/
theorem closedMap_range (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (x : LinearMap.range (right k (n+2))) :
    x ∈ LinearMap.range (closedMap g ρ hg hr a b k n) ↔ x.val ∈ closedSupport n := by
  rw [← projectedExtension_range (Verification.PathRightEndpoint.projection k)
    (Verification.PathRightEndpoint.projection_mem_layer k) n x]
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨recursionEquiv g ρ hg hr a b k n y,rfl⟩
  · rintro ⟨y,hy⟩
    refine ⟨(recursionEquiv g ρ hg hr a b k n).symm y,?_⟩
    change rightExtension k n (recursionEquiv g ρ hg hr a b k n
      ((recursionEquiv g ρ hg hr a b k n).symm y))=x
    rw [LinearEquiv.apply_symm_apply]
    exact hy

theorem closedMap_differential (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (hk : k*k=ρ*k) :
    (imageDifferential (right k (n+2)) (differential g ρ (n+2))).comp
      (closedMap g ρ hg hr a b k n)=
        (closedMap g ρ hg hr a b k n).comp
          (imageDifferential (right (flipConstant g ρ (signAt a b (n+1)) k) n) (differential g ρ n)) := by
  apply LinearMap.ext
  intro x
  have he (y : LinearMap.range (right k n)) :
      imageDifferential (right k (n+2)) (differential g ρ (n+2)) (rightExtension k n y)=
        rightExtension k n (g • imageDifferential (right k n) (differential g ρ n) y) :=
    LinearMap.congr_fun (projectedExtension_differential (Verification.PathRightEndpoint.projection k)
      (Verification.PathRightEndpoint.projection_mem_layer k) g ρ n) y
  have ht (y : LinearMap.range (right k n)) :
      imageDifferential (right k n) (differential g ρ n) (rightTwist g hg k n y)=
        g • rightTwist g hg k n (imageDifferential (right k n) (differential g ρ n) y) :=
    LinearMap.congr_fun (projectedTwist_differential (Verification.PathRightEndpoint.projection k)
      (Verification.PathRightEndpoint.projection_mem_layer k) g ρ hg n) y
  have hs := LinearMap.congr_fun (rightSign_differential g ρ hg hr a b k n hk) x
  change imageDifferential (right k n) (differential g ρ n) (rightSignEquiv g ρ hg hr a b k n x)=
    rightSignEquiv g ρ hg hr a b k n
      (imageDifferential (right (flipConstant g ρ (signAt a b (n+1)) k) n) (differential g ρ n) x) at hs
  change imageDifferential (right k (n+2)) (differential g ρ (n+2))
    (rightExtension k n (rightTwist g hg k n (rightSignEquiv g ρ hg hr a b k n x)))=_
  rw [he,ht,hs,smul_smul,hg,one_smul]
  rfl

/-- An actual equivalence onto the computed closed summand of the endpoint quotient. -/
noncomputable def closedEquiv (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) :
    LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n) ≃ₗ[R]
      LinearMap.range (closedMap g ρ hg hr a b k n) :=
  LinearEquiv.ofInjective _ (closedMap_injective g ρ hg hr a b k n)

#print axioms rightExtension
#print axioms rightTwist
#print axioms recursionEquiv
#print axioms closedMap
#print axioms closedMap_injective
#print axioms closedMap_range
#print axioms closedMap_differential
#print axioms closedEquiv

end Verification.PathRightClosedRecursion
