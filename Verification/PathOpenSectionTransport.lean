/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenSections
import Verification.PathOpenDataTransport

/-!
# Path Open Section Transport

Actual sections transported together with the literal endpoint constants.
-/

namespace Verification.PathOpenSectionTransport

open Verification.PathEndpointTotal Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathOpenBoth Verification.PathOpenSections Verification.PathOpenDataTransport

variable {R : Type*} [CommRing R]

noncomputable def rightTargetSection (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n : ℕ) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) :
    {S : (Bool → LinearMap.range (right target n)) →ₗ[R] LinearMap.range (right source (n+1)) //
      (rightTarget g ρ hg hr a b source target n hk h).map.comp S=LinearMap.id} := by
  subst target
  exact ⟨rightSection g ρ hg hr a b source n,rightData_section g ρ hg hr a b source n hk⟩

noncomputable def bothTargetSection (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n : ℕ) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) :
    {S : LinearMap.range (right target n) →ₗ[R] LinearMap.range (bothProjection source (n+1)) //
      (bothTarget g ρ hg hr a b source target n hk h).map.comp S=LinearMap.id} := by
  subst target
  exact ⟨bothSection g ρ hg hr a b source n,bothData_section g ρ hg hr a b source n hk⟩

noncomputable def bothTargetSectionSize (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n m : ℕ) (hm : n+1=m) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) :
    {S : LinearMap.range (right target n) →ₗ[R] LinearMap.range (bothProjection source m) //
      (bothTargetSize g ρ hg hr a b source target n m hm hk h).map.comp S=LinearMap.id} := by
  subst m
  exact bothTargetSection g ρ hg hr a b source target n hk h

#print axioms rightTargetSection
#print axioms bothTargetSection
#print axioms bothTargetSectionSize

end Verification.PathOpenSectionTransport
