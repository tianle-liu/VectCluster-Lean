/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathProjectedTwist

/-!
# Path Both Closed Recursion

The complete closed recursion for both endpoint quotient relations.
-/

namespace Verification.PathBothClosedRecursion

open Classical Verification.PathCochains Verification.PathRhoFinite
  Verification.PathEndpointTotal Verification.PathEndpointComplex Verification.PathAffineLeftEndpoint
  Verification.PathAffineRightEndpoint Verification.PathBothSignQuotients Verification.PathClosedEmbedding
  Verification.PathClosedEndpointTransport Verification.PathProjectedTwist

variable {R : Type*} [CommRing R]

noncomputable def wordProjection (l r : R) : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  (Verification.PathLeftEndpoint.projection l).comp (Verification.PathRightEndpoint.projection r)

theorem wordProjection_mem (l r : R) (n : ℕ) (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    wordProjection l r x ∈ layer (R := R) n :=
  Verification.PathLeftEndpoint.projection_mem_layer l n _
    (Verification.PathRightEndpoint.projection_mem_layer r n x hx)

noncomputable def pairProjection (l r : R) (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) n :=
  (left l n).comp (right r n)

theorem pairProjection_totalMap (l r : R) (n : ℕ) :
    pairProjection l r n=totalMap (wordProjection l r) (wordProjection_mem l r) n := rfl

noncomputable def bothExtension (l r : R) (n : ℕ) :
    LinearMap.range (pairProjection l r n) →ₗ[R] LinearMap.range (pairProjection l r (n+2)) :=
  projectedExtension (wordProjection l r) (wordProjection_mem l r) n

noncomputable def bothTwist (g : R) (hg : g*g=1) (l r : R) (n : ℕ) :
    LinearMap.range (pairProjection l r n) ≃ₗ[R] LinearMap.range (pairProjection l r n) :=
  projectedTwistEquiv (wordProjection l r) (wordProjection_mem l r) g hg n

variable (g ρ : R)

noncomputable def recursionEquiv (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) :
    LinearMap.range (pairProjection (flipConstant g ρ a l)
      (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m)) ≃ₗ[R]
        LinearMap.range (pairProjection l r (2*m)) :=
  (bothSignEquiv g ρ hg hr a b l r m).trans (bothTwist g hg l r (2*m))

noncomputable def closedMap (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) :
    LinearMap.range (pairProjection (flipConstant g ρ a l)
      (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m)) →ₗ[R]
        LinearMap.range (pairProjection l r (2*m+2)) :=
  (bothExtension l r (2*m)).comp (recursionEquiv g ρ hg hr a b l r m).toLinearMap

theorem closedMap_injective (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) : Function.Injective (closedMap g ρ hg hr a b l r m) :=
  (projectedExtension_injective (wordProjection l r) (wordProjection_mem l r) (2*m)).comp
    (recursionEquiv g ρ hg hr a b l r m).injective

theorem closedMap_range (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) (x : LinearMap.range (pairProjection l r (2*m+2))) :
    x ∈ LinearMap.range (closedMap g ρ hg hr a b l r m) ↔ x.val ∈ closedSupport (2*m) := by
  rw [← projectedExtension_range (wordProjection l r) (wordProjection_mem l r) (2*m) x]
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨recursionEquiv g ρ hg hr a b l r m y,rfl⟩
  · rintro ⟨y,hy⟩
    refine ⟨(recursionEquiv g ρ hg hr a b l r m).symm y,?_⟩
    change bothExtension l r (2*m) (recursionEquiv g ρ hg hr a b l r m
      ((recursionEquiv g ρ hg hr a b l r m).symm y))=x
    rw [LinearEquiv.apply_symm_apply]
    exact hy

theorem closedMap_differential (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ)
    (he : -g*l=l) (hl : l*l=ρ*l) (hk : r*r=ρ*r) :
    (imageDifferential (pairProjection l r (2*m+2)) (differential g ρ (2*m+2))).comp
      (closedMap g ρ hg hr a b l r m)=
        (closedMap g ρ hg hr a b l r m).comp
          (imageDifferential (pairProjection (flipConstant g ρ a l)
            (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m)) (differential g ρ (2*m))) := by
  apply LinearMap.ext
  intro x
  have hE (y : LinearMap.range (pairProjection l r (2*m))) :
      imageDifferential (pairProjection l r (2*m+2)) (differential g ρ (2*m+2))
        (bothExtension l r (2*m) y)=
          bothExtension l r (2*m) (g • imageDifferential (pairProjection l r (2*m)) (differential g ρ (2*m)) y) :=
    LinearMap.congr_fun (projectedExtension_differential (wordProjection l r) (wordProjection_mem l r) g ρ (2*m)) y
  have ht (y : LinearMap.range (pairProjection l r (2*m))) :
      imageDifferential (pairProjection l r (2*m)) (differential g ρ (2*m)) (bothTwist g hg l r (2*m) y)=
        g • bothTwist g hg l r (2*m) (imageDifferential (pairProjection l r (2*m)) (differential g ρ (2*m)) y) :=
    LinearMap.congr_fun (projectedTwist_differential (wordProjection l r) (wordProjection_mem l r) g ρ hg (2*m)) y
  have hs := LinearMap.congr_fun (bothSign_differential g ρ hg hr a b l r m he hl hk) x
  change imageDifferential (pairProjection l r (2*m)) (differential g ρ (2*m)) (bothSignEquiv g ρ hg hr a b l r m x)=
    bothSignEquiv g ρ hg hr a b l r m
      (imageDifferential (pairProjection (flipConstant g ρ a l)
        (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m)) (differential g ρ (2*m)) x) at hs
  change imageDifferential (pairProjection l r (2*m+2)) (differential g ρ (2*m+2))
    (bothExtension l r (2*m) (bothTwist g hg l r (2*m) (bothSignEquiv g ρ hg hr a b l r m x)))=_
  rw [hE,ht,hs,smul_smul,hg,one_smul]
  rfl

noncomputable def closedEquiv (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) :
    LinearMap.range (pairProjection (flipConstant g ρ a l)
      (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m)) ≃ₗ[R]
        LinearMap.range (closedMap g ρ hg hr a b l r m) :=
  LinearEquiv.ofInjective _ (closedMap_injective g ρ hg hr a b l r m)

#print axioms wordProjection
#print axioms wordProjection_mem
#print axioms pairProjection
#print axioms pairProjection_totalMap
#print axioms bothExtension
#print axioms bothTwist
#print axioms recursionEquiv
#print axioms closedMap
#print axioms closedMap_injective
#print axioms closedMap_range
#print axioms closedMap_differential
#print axioms closedEquiv

end Verification.PathBothClosedRecursion
