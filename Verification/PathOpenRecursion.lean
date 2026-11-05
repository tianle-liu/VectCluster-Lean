/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenBoth
import Verification.PathOpenSignTransport
import Verification.PathOpenData

/-!
# Path Open Recursion

Surjective, differential-compatible open recursions with exactly the
original closed support as kernel. Affine coordinate signs are fully included.
-/

namespace Verification.PathOpenRecursion

open Classical Verification.PathCochains Verification.PathRhoFaces
  Verification.PathEndpointTotal Verification.PathEndpointComplex
  Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathEndpointClosedData Verification.PathOpenData
  Verification.PathOpenRight Verification.PathOpenBoth Verification.PathOpenSignTransport

variable {R : Type*} [CommRing R]

noncomputable def torusDifferential (g ρ k : R) (n : ℕ) :
    (Bool → LinearMap.range (right k n)) →ₗ[R] (Bool → LinearMap.range (right k n)) :=
  LinearMap.pi (fun bit => (imageDifferential (right k n) (differential g ρ n)).comp (LinearMap.proj bit))

noncomputable def torusEquiv (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) :
    (Bool → LinearMap.range (right k n)) ≃ₗ[R]
      (Bool → LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n)) :=
  LinearEquiv.piCongrRight (fun bit => normalizedEquiv g ρ hg hr a b k n bit)

noncomputable def rightData (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (hk : k*k=ρ*k) :
    OpenData (R := R) (M := LinearMap.range (right k (n+1)))
      (N := Bool → LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
      (imageDifferential (right k (n+1)) (differential g ρ (n+1)))
      (torusDifferential g ρ (flipConstant g ρ (signAt a b (n+1)) k) n)
      (rightSupport k (n+1)) where
  map := (torusEquiv g ρ hg hr a b k n).toLinearMap.comp (rightProjection k n)
  surjective := (torusEquiv g ρ hg hr a b k n).surjective.comp (rightProjection_surjective k n)
  kernel_iff x := by
    change torusEquiv g ρ hg hr a b k n (rightProjection k n x)=0 ↔
      ∀ I, 1 ∉ I.val → x.val I=0
    rw [← rightProjection_zero_iff k n x]
    exact (torusEquiv g ρ hg hr a b k n).map_eq_zero_iff
  intertwining := by
    apply LinearMap.ext
    intro x
    funext bit
    have hq := congrFun (LinearMap.congr_fun (rightProjection_differential k g ρ n) x) bit
    have hs := LinearMap.congr_fun (normalized_intertwining g ρ hg hr a b k n bit hk)
      (rightProjection k n x bit)
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearMap.smul_apply] at hs
    change normalizedEquiv g ρ hg hr a b k n bit
      (rightProjection k n (imageDifferential _ _ x) bit)=_
    rw [show rightProjection k n (imageDifferential _ _ x) bit=
      phase (-g) bit • imageDifferential (right k n) (differential g ρ n) (rightProjection k n x bit) from hq]
    exact hs.symm

noncomputable def bothData (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (hk : k*k=ρ*k) :
    OpenData (R := R) (M := LinearMap.range (bothProjection k (n+1)))
      (N := LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
      (imageDifferential (bothProjection k (n+1)) (differential g ρ (n+1)))
      (imageDifferential (right (flipConstant g ρ (signAt a b (n+1)) k) n) (differential g ρ n))
      (bothSupport 0 k (n+1)) where
  map := (normalizedEquiv g ρ hg hr a b k n false).toLinearMap.comp (bothRestriction k n)
  surjective := (normalizedEquiv g ρ hg hr a b k n false).surjective.comp (bothRestriction_surjective k n)
  kernel_iff x := by
    change normalizedEquiv g ρ hg hr a b k n false (bothRestriction k n x)=0 ↔
      ∀ I, 1 ∉ I.val → x.val I=0
    rw [← bothRestriction_zero_iff k n x]
    exact (normalizedEquiv g ρ hg hr a b k n false).map_eq_zero_iff
  intertwining := by
    apply LinearMap.ext
    intro x
    have hq := LinearMap.congr_fun (bothRestriction_differential k g ρ n) x
    have hs := LinearMap.congr_fun (normalized_intertwining g ρ hg hr a b k n false hk)
      (bothRestriction k n x)
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearMap.smul_apply,
      phase,Bool.false_eq_true,↓reduceIte,one_smul] at hs hq
    change normalizedEquiv g ρ hg hr a b k n false (bothRestriction k n (imageDifferential _ _ x))=_
    rw [hq]
    exact hs.symm

#print axioms torusDifferential
#print axioms torusEquiv
#print axioms rightData
#print axioms bothData

end Verification.PathOpenRecursion
