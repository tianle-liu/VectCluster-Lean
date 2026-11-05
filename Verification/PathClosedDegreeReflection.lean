/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathProjectedDegree

/-!
# Path Closed Degree Reflection

Closed recursion also reflects the shifted degree, via its actual
restriction and inverse signed coordinates. This controls the closed
coordinate of the split cone, not only its forward embedding.
-/

namespace Verification.PathClosedDegreeReflection

open Verification.PathCochains Verification.PathEndpointTotal Verification.PathRecursionDegree
  Verification.PathProjectedDegree Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathClosedEmbedding Verification.PathBothClosedRecursion

variable {R : Type*} [CommRing R]

theorem right_inverse_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (p : ℤ)
    (x : LinearMap.range (right k n)) (hx : TotalDegree n p x.val) :
    TotalDegree n p ((Verification.PathRightClosedRecursion.recursionEquiv g ρ hg hr a b k n).symm x).val :=
  right_degree _ n p _ (sign_degree g ρ a b n p _ (twist_degree g n p _ hx))

theorem both_inverse_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) (p : ℤ)
    (x : LinearMap.range (pairProjection l r (2*m))) (hx : TotalDegree (2*m) p x.val) :
    TotalDegree (2*m) p ((recursionEquiv g ρ hg hr a b l r m).symm x).val :=
  left_degree _ (2*m) p _ (right_degree _ (2*m) p _
    (sign_degree g ρ a b (2*m) p _ (twist_degree g (2*m) p _ hx)))

theorem right_reflects_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (p : ℤ)
    (x : LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
    (hx : TotalDegree (n+2) (p+1)
      (Verification.PathRightClosedRecursion.closedMap g ρ hg hr a b k n x).val) :
    TotalDegree n p x.val := by
  have hh := closed_restriction_degree n p _ hx
  change TotalDegree n p (restriction n (extension n
    (Verification.PathRightClosedRecursion.recursionEquiv g ρ hg hr a b k n x).val)) at hh
  have he := LinearMap.congr_fun (restriction_extension (R := R) n)
    (Verification.PathRightClosedRecursion.recursionEquiv g ρ hg hr a b k n x).val
  simp only [LinearMap.comp_apply,LinearMap.id_apply] at he
  rw [he] at hh
  have hk := right_inverse_degree g ρ hg hr a b k n p _ hh
  simpa only [LinearEquiv.symm_apply_apply] using hk

theorem both_reflects_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) (p : ℤ)
    (x : LinearMap.range (pairProjection (flipConstant g ρ a l)
      (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m)))
    (hx : TotalDegree (2*m+2) (p+1) (closedMap g ρ hg hr a b l r m x).val) :
    TotalDegree (2*m) p x.val := by
  have hh := closed_restriction_degree (2*m) p _ hx
  change TotalDegree (2*m) p (restriction (2*m) (extension (2*m)
    (recursionEquiv g ρ hg hr a b l r m x).val)) at hh
  have he := LinearMap.congr_fun (restriction_extension (R := R) (2*m))
    (recursionEquiv g ρ hg hr a b l r m x).val
  simp only [LinearMap.comp_apply,LinearMap.id_apply] at he
  rw [he] at hh
  have hk := both_inverse_degree g ρ hg hr a b l r m p _ hh
  simpa only [LinearEquiv.symm_apply_apply] using hk

#print axioms right_inverse_degree
#print axioms both_inverse_degree
#print axioms right_reflects_degree
#print axioms both_reflects_degree

end Verification.PathClosedDegreeReflection
