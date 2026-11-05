/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathProjectedDegree
import Verification.PathActualOpenSections
import Verification.PathClosedZ
import Verification.PathClosedY

/-!
# Path Degree Transport

Degree support transported along the proved endpoint constant equalities.
All scalar and size equalities are handled before their path specialization.
-/

namespace Verification.PathDegreeTransport

open Verification.PathEndpointTotal Verification.PathRecursionDegree Verification.PathProjectedDegree
  Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathClosedDataTransport Verification.PathOpenDataTransport Verification.PathOpenSectionTransport
  Verification.PathBothClosedRecursion Verification.PathOpenBoth

variable {R : Type*} [CommRing R]

theorem rightSource_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n : ℕ) (hk : target*target=ρ*target)
    (he : flipConstant g ρ (signAt a b (n+1)) target=source) (p : ℤ)
    (x : LinearMap.range (right source n)) (hx : TotalDegree n p x.val) :
    TotalDegree (n+2) (p+1) ((rightSource g ρ hg hr a b source target n hk he).map x).val := by
  subst source
  exact right_closed_degree g ρ hg hr a b target n p x hx

theorem bothSource_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (sourceL sourceR l r : R) (m : ℕ)
    (he : -g*l=l) (hl : l*l=ρ*l) (hk : r*r=ρ*r)
    (hleft : flipConstant g ρ a l=sourceL)
    (hright : flipConstant g ρ (signAt a b (2*m+1)) r=sourceR) (p : ℤ)
    (x : LinearMap.range (pairProjection sourceL sourceR (2*m))) (hx : TotalDegree (2*m) p x.val) :
    TotalDegree (2*m+2) (p+1)
      ((bothSource g ρ hg hr a b sourceL sourceR l r m he hl hk hleft hright).map x).val := by
  subst sourceL
  subst sourceR
  exact both_closed_degree g ρ hg hr a b l r m p x hx

theorem bothSourceSize_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (sourceL sourceR l r : R) (m n : ℕ) (hlen : 2*m+2=n)
    (he : -g*l=l) (hl : l*l=ρ*l) (hk : r*r=ρ*r)
    (hleft : flipConstant g ρ a l=sourceL)
    (hright : flipConstant g ρ (signAt a b (2*m+1)) r=sourceR) (p : ℤ)
    (x : LinearMap.range (pairProjection sourceL sourceR (2*m))) (hx : TotalDegree (2*m) p x.val) :
    TotalDegree n (p+1)
      ((bothSourceSize g ρ hg hr a b sourceL sourceR l r m n hlen he hl hk hleft hright).map x).val := by
  subst n
  exact bothSource_degree g ρ hg hr a b sourceL sourceR l r m he hl hk hleft hright p x hx

theorem rightTarget_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n : ℕ) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) (p : ℤ)
    (x : LinearMap.range (right source (n+1))) (hx : TotalDegree (n+1) p x.val) (bit : Bool) :
    TotalDegree n p ((rightTarget g ρ hg hr a b source target n hk h).map x bit).val := by
  subst target
  exact right_open_degree g ρ hg hr a b source n hk p x hx bit

theorem bothTargetSize_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n m : ℕ) (hm : n+1=m) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) (p : ℤ)
    (x : LinearMap.range (bothProjection source m)) (hx : TotalDegree m p x.val) :
    TotalDegree n p ((bothTargetSize g ρ hg hr a b source target n m hm hk h).map x).val := by
  subst m
  subst target
  exact both_open_degree g ρ hg hr a b source n hk p x hx

theorem rightTargetSection_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n : ℕ) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) (p : ℤ)
    (x : Bool → LinearMap.range (right target n)) (hx : ∀ bit, TotalDegree n p (x bit).val) :
    TotalDegree (n+1) p ((rightTargetSection g ρ hg hr a b source target n hk h).val x).val := by
  subst target
  exact right_section_degree g ρ hg hr a b source n p x hx

theorem bothTargetSectionSize_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n m : ℕ) (hm : n+1=m) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) (p : ℤ)
    (x : LinearMap.range (right target n)) (hx : TotalDegree n p x.val) :
    TotalDegree m p ((bothTargetSectionSize g ρ hg hr a b source target n m hm hk h).val x).val := by
  subst m
  subst target
  exact both_section_degree g ρ hg hr a b source n p x hx

#print axioms rightSource_degree
#print axioms bothSource_degree
#print axioms bothSourceSize_degree
#print axioms rightTarget_degree
#print axioms bothTargetSize_degree
#print axioms rightTargetSection_degree
#print axioms bothTargetSectionSize_degree

end Verification.PathDegreeTransport
