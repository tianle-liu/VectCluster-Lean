/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClosedEndpointTransport

/-!
# Path Projected Twist

The normal-degree compensation is an actual automorphism of every
word-projector image and has the required twisted differential identity.
-/

namespace Verification.PathProjectedTwist

open Classical Verification.PathCochains Verification.PathRhoFinite
  Verification.PathClosedSignedComplex Verification.PathEndpointTotal Verification.PathEndpointComplex
  Verification.PathClosedEndpointTransport

variable {R : Type*} [CommRing R]
variable (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
variable (hP : ∀ n x, x ∈ layer (R := R) n → P x ∈ layer n)
variable (g ρ : R)

noncomputable def projectedTwist (n : ℕ) :
    LinearMap.range (totalMap P hP n) →ₗ[R] LinearMap.range (totalMap P hP n) :=
  LinearMap.codRestrict _ ((degreeTwist g n).comp (LinearMap.range (totalMap P hP n)).subtype)
    (fun x => by
      obtain ⟨y,hy⟩ := x.property
      refine ⟨degreeTwist g n y,?_⟩
      change totalMap P hP n (degreeTwist g n y)=degreeTwist g n x.val
      rw [show totalMap P hP n (degreeTwist g n y)=degreeTwist g n (totalMap P hP n y) from
        LinearMap.congr_fun (totalMap_twist P hP g n) y,hy])

theorem projectedTwist_squared (hg : g*g=1) (n : ℕ) :
    (projectedTwist P hP g n).comp (projectedTwist P hP g n)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (degreeTwist_squared g hg n) x.val

noncomputable def projectedTwistEquiv (hg : g*g=1) (n : ℕ) :
    LinearMap.range (totalMap P hP n) ≃ₗ[R] LinearMap.range (totalMap P hP n) :=
  LinearEquiv.ofLinear (projectedTwist P hP g n) (projectedTwist P hP g n)
    (projectedTwist_squared P hP g hg n) (projectedTwist_squared P hP g hg n)

theorem projectedTwist_differential (hg : g*g=1) (n : ℕ) :
    (imageDifferential (totalMap P hP n) (differential g ρ n)).comp (projectedTwist P hP g n)=
      g • (projectedTwist P hP g n).comp
        (imageDifferential (totalMap P hP n) (differential g ρ n)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change totalMap P hP n (differential g ρ n (degreeTwist g n x.val))=
    g • degreeTwist g n (totalMap P hP n (differential g ρ n x.val))
  have hd := LinearMap.congr_fun (differential_twist g ρ hg n) x.val
  change differential g ρ n (degreeTwist g n x.val)=g • degreeTwist g n (differential g ρ n x.val) at hd
  rw [hd,map_smul]
  congr 1
  exact LinearMap.congr_fun (totalMap_twist P hP g n) (differential g ρ n x.val)

#print axioms projectedTwist
#print axioms projectedTwist_squared
#print axioms projectedTwistEquiv
#print axioms projectedTwist_differential

end Verification.PathProjectedTwist
