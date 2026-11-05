/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignQuotients

/-!
# Path Both Sign Quotients

Actual two-endpoint quotient equivalences for the complete affine sign map.
The constants are transformed explicitly; no quotient conjugacy is assumed.
-/

namespace Verification.PathBothSignQuotients

open Classical Verification.PathCochains Verification.PathEndpointTotal
  Verification.PathEndpointComplex Verification.PathAffineLeftEndpoint
  Verification.PathAffineRightEndpoint Verification.PathGlobalAffineSigns
  Verification.PathSignQuotients

variable {R : Type*} [CommRing R]

noncomputable def twoProjection (l r : R) (m : ℕ) :
    Total (R := R) (2*m) →ₗ[R] Total (R := R) (2*m) :=
  (left l (2*m)).comp (right r (2*m))

theorem twoProjection_idempotent (l r : R) (m : ℕ) :
    (twoProjection l r m).comp (twoProjection l r m)=twoProjection l r m :=
  product_idempotent _ _ (left_idempotent _ _) (right_idempotent _ _)
    (endpoints_commute l r m)

theorem twoProjection_quotient (g ρ l r : R) (m : ℕ)
    (he : -g*l=l) (hl : l*l=ρ*l) (hr : r*r=ρ*r) :
    (twoProjection l r m).comp ((differential g ρ (2*m)).comp (twoProjection l r m))=
      (twoProjection l r m).comp (differential g ρ (2*m)) :=
  product_quotient _ _ _ (Verification.PathEndpointTotal.left_quotient l g ρ (2*m) he hl)
    (Verification.PathEndpointTotal.right_quotient r g ρ (2*m) hr) (endpoints_commute l r m)

variable (g ρ : R)

theorem both_reverse (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) :
    (twoProjection (flipConstant g ρ a l) (flipConstant g ρ (signAt a b (2*m+1)) r) m).comp
      ((totalSign g ρ a b (2*m)).comp (twoProjection l r m))=
        (twoProjection (flipConstant g ρ a l) (flipConstant g ρ (signAt a b (2*m+1)) r) m).comp
          (totalSign g ρ a b (2*m)) := by
  have hh := Verification.PathGlobalEndpointSigns.both_quotient g ρ a b
    (flipConstant g ρ a l) (flipConstant g ρ (signAt a b (2*m+1)) r) m
  rw [flipConstant_squared g ρ hg hr,flipConstant_squared g ρ hg hr] at hh
  exact hh

/-- A true equivalence between the two actual endpoint quotient images. -/
noncomputable def bothSignEquiv (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) :
    LinearMap.range (twoProjection (flipConstant g ρ a l)
      (flipConstant g ρ (signAt a b (2*m+1)) r) m) ≃ₗ[R]
        LinearMap.range (twoProjection l r m) :=
  imageEquiv _ _ (totalSign g ρ a b (2*m)) (twoProjection_idempotent _ _ _)
    (twoProjection_idempotent _ _ _) (totalSign_squared g ρ hg hr a b (2*m))
      (both_reverse g ρ hg hr a b l r m)
        (Verification.PathGlobalEndpointSigns.both_quotient g ρ a b l r m)

theorem bothSign_differential (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ)
    (he : -g*l=l) (hl : l*l=ρ*l) (hk : r*r=ρ*r) :
    (imageDifferential (twoProjection l r m) (differential g ρ (2*m))).comp
      (bothSignEquiv g ρ hg hr a b l r m).toLinearMap=
        (bothSignEquiv g ρ hg hr a b l r m).toLinearMap.comp
          (imageDifferential (twoProjection (flipConstant g ρ a l)
            (flipConstant g ρ (signAt a b (2*m+1)) r) m) (differential g ρ (2*m))) :=
  imageMap_intertwining _ _ _ _ (twoProjection_quotient g ρ l r m he hl hk)
    (differential_intertwining g ρ hg hr a b (2*m))
      (Verification.PathGlobalEndpointSigns.both_quotient g ρ a b l r m)

#print axioms twoProjection
#print axioms twoProjection_idempotent
#print axioms twoProjection_quotient
#print axioms both_reverse
#print axioms bothSignEquiv
#print axioms bothSign_differential

end Verification.PathBothSignQuotients
