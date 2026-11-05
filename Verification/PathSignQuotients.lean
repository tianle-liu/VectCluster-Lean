/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathGlobalEndpointSigns
import Verification.PathEndpointComplex

/-!
# Path Sign Quotients

Actual equivalences of endpoint quotient modules under full affine signs,
including equality of their actual rho differentials.
-/

namespace Verification.PathSignQuotients

open Classical Verification.PathCochains Verification.PathEndpointTotal
  Verification.PathEndpointComplex Verification.PathAffineLeftEndpoint
  Verification.PathAffineRightEndpoint Verification.PathGlobalAffineSigns

variable {R : Type*} [CommRing R]

section Images
variable {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def imageMap (P Q S : M →ₗ[R] M) : LinearMap.range P →ₗ[R] LinearMap.range Q :=
  LinearMap.codRestrict _ (Q.comp (S.comp (LinearMap.range P).subtype)) (fun x => ⟨S x.val,rfl⟩)

theorem range_fixed (P : M →ₗ[R] M) (hP : P.comp P=P) (x : LinearMap.range P) : P x.val=x.val := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun hP y

theorem imageMap_inverse (P Q S : M →ₗ[R] M) (hP : P.comp P=P)
    (hS : S.comp S=LinearMap.id) (hPSQ : P.comp (S.comp Q)=P.comp S) :
    (imageMap Q P S).comp (imageMap P Q S)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change P (S (Q (S x.val)))=x.val
  have hh := LinearMap.congr_fun hPSQ (S x.val)
  change P (S (Q (S x.val)))=P (S (S x.val)) at hh
  rw [hh]
  have hs := LinearMap.congr_fun hS x.val
  change S (S x.val)=x.val at hs
  rw [hs]
  exact range_fixed P hP x

noncomputable def imageEquiv (P Q S : M →ₗ[R] M) (hP : P.comp P=P) (hQ : Q.comp Q=Q)
    (hS : S.comp S=LinearMap.id) (hPSQ : P.comp (S.comp Q)=P.comp S)
    (hQSP : Q.comp (S.comp P)=Q.comp S) : LinearMap.range P ≃ₗ[R] LinearMap.range Q :=
  LinearEquiv.ofLinear (imageMap P Q S) (imageMap Q P S)
    (imageMap_inverse Q P S hQ hS hQSP) (imageMap_inverse P Q S hP hS hPSQ)

/-- The image equivalence intertwines the actual projected differentials. -/
theorem imageMap_intertwining (P Q S D : M →ₗ[R] M)
    (hQ : Q.comp (D.comp Q)=Q.comp D) (hS : D.comp S=S.comp D)
    (hQSP : Q.comp (S.comp P)=Q.comp S) :
    (imageDifferential Q D).comp (imageMap P Q S)=
      (imageMap P Q S).comp (imageDifferential P D) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Q (D (Q (S x.val)))=Q (S (P (D x.val)))
  have hq (y : M) : Q (D (Q y))=Q (D y) := LinearMap.congr_fun hQ y
  have hs (y : M) : D (S y)=S (D y) := LinearMap.congr_fun hS y
  have hp (y : M) : Q (S (P y))=Q (S y) := LinearMap.congr_fun hQSP y
  rw [hq,hs,hp]
end Images

variable (g ρ : R)

theorem right_reverse (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool) (k : R) (n : ℕ) :
    (right (flipConstant g ρ (signAt a b (n+1)) k) n).comp
      ((totalSign g ρ a b n).comp (right k n))=
        (right (flipConstant g ρ (signAt a b (n+1)) k) n).comp (totalSign g ρ a b n) := by
  have hh := Verification.PathGlobalEndpointSigns.right_quotient g ρ a b
    (flipConstant g ρ (signAt a b (n+1)) k) n
  rw [flipConstant_squared g ρ hg hr] at hh
  exact hh

/-- A genuine finite quotient-module equivalence with the transformed endpoint constant. -/
noncomputable def rightSignEquiv (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool) (k : R) (n : ℕ) :
    LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n) ≃ₗ[R]
      LinearMap.range (right k n) :=
  imageEquiv _ _ (totalSign g ρ a b n) (right_idempotent _ _) (right_idempotent _ _)
    (totalSign_squared g ρ hg hr a b n) (right_reverse g ρ hg hr a b k n)
      (Verification.PathGlobalEndpointSigns.right_quotient g ρ a b k n)

theorem rightSign_differential (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (hk : k*k=ρ*k) :
    (imageDifferential (right k n) (differential g ρ n)).comp
      (rightSignEquiv g ρ hg hr a b k n).toLinearMap=
        (rightSignEquiv g ρ hg hr a b k n).toLinearMap.comp
          (imageDifferential (right (flipConstant g ρ (signAt a b (n+1)) k) n) (differential g ρ n)) :=
  imageMap_intertwining _ _ _ _ (Verification.PathEndpointTotal.right_quotient k g ρ n hk)
    (differential_intertwining g ρ hg hr a b n)
      (Verification.PathGlobalEndpointSigns.right_quotient g ρ a b k n)

#print axioms imageMap
#print axioms range_fixed
#print axioms imageMap_inverse
#print axioms imageEquiv
#print axioms imageMap_intertwining
#print axioms right_reverse
#print axioms rightSignEquiv
#print axioms rightSign_differential

end Verification.PathSignQuotients
