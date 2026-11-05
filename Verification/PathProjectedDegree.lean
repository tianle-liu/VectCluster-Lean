/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRecursionDegree
import Verification.PathOpenSections
import Verification.PathBothClosedRecursion

/-!
# Path Projected Degree

Degree control survives the literal endpoint image maps, affine signs,
and the explicit open sections used in the recursive cone coordinates.
-/

namespace Verification.PathProjectedDegree

open Verification.PathCochains Verification.PathRhoFinite Verification.PathEndpointTotal
  Verification.PathRecursionDegree Verification.PathGlobalAffineSigns
  Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathClosedSignedComplex Verification.PathOpenSignTransport

variable {R : Type*} [CommRing R]

theorem degree_add {n : ℕ} {p : ℤ} {x y : Total (R := R) n}
    (hx : TotalDegree n p x) (hy : TotalDegree n p y) : TotalDegree n p (x+y) := by
  intro I hI
  simp only [Pi.add_apply,hx I hI,hy I hI,add_zero]

theorem degree_sub {n : ℕ} {p : ℤ} {x y : Total (R := R) n}
    (hx : TotalDegree n p x) (hy : TotalDegree n p y) : TotalDegree n p (x-y) := by
  intro I hI
  simp only [Pi.sub_apply,hx I hI,hy I hI,sub_self]

theorem totalMap_degree (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
    (hP : ∀ n x, x ∈ layer (R := R) n → P x ∈ layer n)
    (n : ℕ) (p : ℤ) (x : Total (R := R) n) (hx : TotalDegree n p x) :
    TotalDegree n p (totalMap P hP n x) := by
  intro I hI
  apply Subtype.ext
  change P (x I).val=0
  rw [hx I hI]
  exact map_zero _

theorem right_degree (k : R) (n : ℕ) (p : ℤ) (x : Total (R := R) n)
    (hx : TotalDegree n p x) : TotalDegree n p (right k n x) :=
  totalMap_degree _ (Verification.PathRightEndpoint.projection_mem_layer k) n p x hx

theorem left_degree (k : R) (n : ℕ) (p : ℤ) (x : Total (R := R) n)
    (hx : TotalDegree n p x) : TotalDegree n p (left k n x) :=
  totalMap_degree _ (Verification.PathLeftEndpoint.projection_mem_layer k) n p x hx

theorem normalized_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (bit : Bool) (p : ℤ)
    (x : LinearMap.range (right k n)) (hx : TotalDegree n p x.val) :
    TotalDegree n p (normalizedEquiv g ρ hg hr a b k n bit x).val :=
  right_degree _ n p _ (sign_degree g ρ a b n p _
    (twist_degree (Verification.PathRhoFaces.phase (-g) bit) n p _ hx))

theorem normalized_symm_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (bit : Bool) (p : ℤ)
    (x : LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
    (hx : TotalDegree n p x.val) :
    TotalDegree n p ((normalizedEquiv g ρ hg hr a b k n bit).symm x).val :=
  twist_degree (Verification.PathRhoFaces.phase (-g) bit) n p _
    (right_degree k n p _ (sign_degree g ρ a b n p _ hx))

theorem right_closed_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (p : ℤ)
    (x : LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
    (hx : TotalDegree n p x.val) :
    TotalDegree (n+2) (p+1)
      (Verification.PathRightClosedRecursion.closedMap g ρ hg hr a b k n x).val :=
  closed_extension_degree n p _ (twist_degree g n p _
    (right_degree k n p _ (sign_degree g ρ a b n p _ hx)))

theorem both_closed_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) (p : ℤ)
    (x : LinearMap.range (Verification.PathBothClosedRecursion.pairProjection
      (flipConstant g ρ a l) (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m)))
    (hx : TotalDegree (2*m) p x.val) :
    TotalDegree (2*m+2) (p+1)
      (Verification.PathBothClosedRecursion.closedMap g ρ hg hr a b l r m x).val :=
  closed_extension_degree (2*m) p _ (twist_degree g (2*m) p _
    (left_degree l (2*m) p _ (right_degree r (2*m) p _ (sign_degree g ρ a b (2*m) p _ hx))))

theorem right_open_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (hk : k*k=ρ*k) (p : ℤ)
    (x : LinearMap.range (right k (n+1))) (hx : TotalDegree (n+1) p x.val) (bit : Bool) :
    TotalDegree n p ((Verification.PathOpenRecursion.rightData g ρ hg hr a b k n hk).map x bit).val :=
  normalized_degree g ρ hg hr a b k n bit p _ (open_restriction_degree n bit p x.val hx)

theorem both_open_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (hk : k*k=ρ*k) (p : ℤ)
    (x : LinearMap.range (Verification.PathOpenBoth.bothProjection k (n+1)))
    (hx : TotalDegree (n+1) p x.val) :
    TotalDegree n p ((Verification.PathOpenRecursion.bothData g ρ hg hr a b k n hk).map x).val :=
  normalized_degree g ρ hg hr a b k n false p _ (open_restriction_degree n false p x.val hx)

theorem right_section_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (p : ℤ)
    (x : Bool → LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
    (hx : ∀ bit, TotalDegree n p (x bit).val) :
    TotalDegree (n+1) p (Verification.PathOpenSections.rightSection g ρ hg hr a b k n x).val :=
  degree_add
    (open_extension_degree n false p _ (normalized_symm_degree g ρ hg hr a b k n false p _ (hx false)))
    (open_extension_degree n true p _ (normalized_symm_degree g ρ hg hr a b k n true p _ (hx true)))

theorem both_section_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (p : ℤ)
    (x : LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
    (hx : TotalDegree n p x.val) :
    TotalDegree (n+1) p (Verification.PathOpenSections.bothSection g ρ hg hr a b k n x).val :=
  open_extension_degree n false p _ (normalized_symm_degree g ρ hg hr a b k n false p _ hx)

#print axioms degree_add
#print axioms degree_sub
#print axioms totalMap_degree
#print axioms right_degree
#print axioms left_degree
#print axioms normalized_degree
#print axioms normalized_symm_degree
#print axioms right_closed_degree
#print axioms both_closed_degree
#print axioms right_open_degree
#print axioms both_open_degree
#print axioms right_section_degree
#print axioms both_section_degree

end Verification.PathProjectedDegree
