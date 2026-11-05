/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClosedDifferential

/-!
# Path Closed Signed Complex

The complete affine coordinate change and normal compensation identify
the shorter path differential with the actual original closed subcomplex.
-/

namespace Verification.PathClosedSignedComplex

open Classical Verification.PathCompression Verification.PathCochains Verification.PathRhoFinite
  Verification.PathGlobalAffineSigns Verification.PathClosedEmbedding Verification.PathClosedDifferential

variable {R : Type*} [CommRing R] (g ρ : R)

noncomputable def degreeTwist (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) n :=
  LinearMap.pi (fun I => g^I.val.card • LinearMap.proj I)

theorem degreeTwist_squared (hg : g*g=1) (n : ℕ) :
    (degreeTwist g n).comp (degreeTwist g n)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext I
  change g^I.val.card • (g^I.val.card • x I)=x I
  rw [smul_smul,← mul_pow,hg,one_pow,one_smul]

noncomputable def degreeTwistEquiv (hg : g*g=1) (n : ℕ) : Total (R := R) n ≃ₗ[R] Total (R := R) n :=
  LinearEquiv.ofLinear (degreeTwist g n) (degreeTwist g n)
    (degreeTwist_squared g hg n) (degreeTwist_squared g hg n)

theorem differential_twist (hg : g*g=1) (n : ℕ) :
    (differential g ρ n).comp (degreeTwist g n)=
      g • (degreeTwist g n).comp (differential g ρ n) := by
  apply LinearMap.ext
  intro x
  funext J
  apply Subtype.ext
  change ambientDifferential g ρ n (inclusion n (degreeTwist g n x)) J=
    g • (g^J.val.card • ambientDifferential g ρ n (inclusion n x) J)
  rw [smul_smul,ambientDifferential_apply,ambientDifferential_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change Verification.PathRhoConfiguration.faceMap g ρ (eraseConfig J j).val j
    (g^(J.val.erase j).card • (x (eraseConfig J j)).val)=_
  rw [map_smul]
  have he : g^(J.val.erase j).card=g*g^J.val.card := by
    rw [← Finset.card_erase_add_one hj,pow_succ]
    calc
      _=g^(J.val.erase j).card*(g*g) := by rw [hg,mul_one]
      _=_ := by ring
  rw [he]
  rfl

noncomputable def signedExtension (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) (n+2) :=
  (extension n).comp ((degreeTwistEquiv g hg n).toLinearMap.comp
    (totalSignEquiv g ρ hg hr a b n).toLinearMap)

theorem signedExtension_differential (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (n : ℕ) :
    (differential g ρ (n+2)).comp (signedExtension g ρ hg hr a b n)=
      (signedExtension g ρ hg hr a b n).comp (differential g ρ n) := by
  apply LinearMap.ext
  intro x
  have he (y : Total (R := R) n) :
      differential g ρ (n+2) (extension n y)=extension n (g • differential g ρ n y) :=
    LinearMap.congr_fun (differential_extension g ρ n) y
  have ht (y : Total (R := R) n) :
      differential g ρ n (degreeTwist g n y)=g • degreeTwist g n (differential g ρ n y) :=
    LinearMap.congr_fun (differential_twist g ρ hg n) y
  have hs (y : Total (R := R) n) :
      differential g ρ n (totalSign g ρ a b n y)=totalSign g ρ a b n (differential g ρ n y) :=
    LinearMap.congr_fun (differential_intertwining g ρ hg hr a b n) y
  change differential g ρ (n+2) (extension n (degreeTwist g n (totalSign g ρ a b n x)))=
    extension n (degreeTwist g n (totalSign g ρ a b n (differential g ρ n x)))
  rw [he,ht,hs,smul_smul,hg,one_smul]

/-- This is a genuine module equivalence onto the actual closed support. -/
noncomputable def closedEquiv (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (n : ℕ) : Total (R := R) n ≃ₗ[R] closedSupport (R := R) n :=
  ((totalSignEquiv g ρ hg hr a b n).trans (degreeTwistEquiv g hg n)).trans
    (LinearEquiv.ofInjective (extension n) (extension_injective n))

noncomputable def closedDifferential (n : ℕ) :
    closedSupport (R := R) n →ₗ[R] closedSupport (R := R) n :=
  (differential g ρ (n+2)).restrict (differential_closedSupport g ρ n)

theorem closedEquiv_differential (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (n : ℕ) :
    (closedDifferential g ρ n).comp (closedEquiv g ρ hg hr a b n).toLinearMap=
      (closedEquiv g ρ hg hr a b n).toLinearMap.comp (differential g ρ n) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (signedExtension_differential g ρ hg hr a b n) x

#print axioms degreeTwist
#print axioms degreeTwist_squared
#print axioms degreeTwistEquiv
#print axioms differential_twist
#print axioms signedExtension
#print axioms signedExtension_differential
#print axioms closedEquiv
#print axioms closedDifferential
#print axioms closedEquiv_differential

end Verification.PathClosedSignedComplex
