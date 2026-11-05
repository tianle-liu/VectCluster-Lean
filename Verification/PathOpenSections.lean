/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenRecursion

/-!
# Path Open Sections

Explicit sections of the actual affine-normalized open restriction maps.
These retain the coordinate formulas needed for filtered recursive cone assembly.
-/

namespace Verification.PathOpenSections

open Verification.PathCochains Verification.PathEndpointTotal Verification.PathEndpointComplex
  Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathOpenRight Verification.PathOpenBoth Verification.PathOpenSignTransport
  Verification.PathOpenRecursion

variable {R : Type*} [CommRing R]
section Generic
variable {M N P : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

theorem section_postcompose (Q : M →ₗ[R] N) (S : N →ₗ[R] M)
    (h : Q.comp S=LinearMap.id) (e : N ≃ₗ[R] P) :
    (e.toLinearMap.comp Q).comp (S.comp e.symm.toLinearMap)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun h (e.symm x)
  simp only [LinearMap.comp_apply,LinearMap.id_apply] at hh
  change e (Q (S (e.symm x)))=x
  rw [hh,LinearEquiv.apply_symm_apply]
end Generic

variable (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool) (k : R) (n : ℕ)

noncomputable def rightSection :
    (Bool → LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n)) →ₗ[R]
      LinearMap.range (right k (n+1)) :=
  (Verification.PathOpenRight.rightSection k n).comp (torusEquiv g ρ hg hr a b k n).symm.toLinearMap

theorem rightData_section (hk : k*k=ρ*k) :
    (Verification.PathOpenRecursion.rightData g ρ hg hr a b k n hk).map.comp
      (rightSection g ρ hg hr a b k n)=LinearMap.id := by
  unfold Verification.PathOpenRecursion.rightData rightSection
  exact section_postcompose (R := R) (M := LinearMap.range (right k (n+1)))
    (N := Bool → LinearMap.range (right k n))
    (P := Bool → LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
    (rightProjection k n) (Verification.PathOpenRight.rightSection k n)
    (rightProjection_section k n) (torusEquiv g ρ hg hr a b k n)

noncomputable def bothSection :
    LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n) →ₗ[R]
      LinearMap.range (bothProjection k (n+1)) :=
  (Verification.PathOpenBoth.bothSection k n).comp
    (normalizedEquiv g ρ hg hr a b k n false).symm.toLinearMap

theorem bothData_section (hk : k*k=ρ*k) :
    (Verification.PathOpenRecursion.bothData g ρ hg hr a b k n hk).map.comp
      (bothSection g ρ hg hr a b k n)=LinearMap.id := by
  unfold Verification.PathOpenRecursion.bothData bothSection
  exact section_postcompose (R := R) (M := LinearMap.range (bothProjection k (n+1)))
    (N := LinearMap.range (right k n))
    (P := LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
    (bothRestriction k n) (Verification.PathOpenBoth.bothSection k n)
    (bothRestriction_section k n) (normalizedEquiv g ρ hg hr a b k n false)

#print axioms section_postcompose
#print axioms rightSection
#print axioms rightData_section
#print axioms bothSection
#print axioms bothData_section

end Verification.PathOpenSections
