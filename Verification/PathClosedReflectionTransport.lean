/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClosedDegreeReflection
import Verification.PathClosedZ
import Verification.PathClosedY

/-!
# Path Closed Reflection Transport

Actual Z/Y closed embeddings reflect their original degree-one shift.
-/

namespace Verification.PathClosedReflectionTransport

open Verification.PathEndpointTotal Verification.PathRecursionDegree Verification.PathClosedDegreeReflection
  Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint Verification.PathClosedDataTransport
  Verification.PathBothClosedRecursion Verification.PathEndpointComplex Verification.PathEndpointRecursionConstants

variable {R : Type*} [CommRing R]

theorem rightSource_reflects (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n : ℕ) (hk : target*target=ρ*target)
    (he : flipConstant g ρ (signAt a b (n+1)) target=source) (p : ℤ)
    (x : LinearMap.range (right source n))
    (hx : TotalDegree (n+2) (p+1) ((rightSource g ρ hg hr a b source target n hk he).map x).val) :
    TotalDegree n p x.val := by
  subst source
  exact right_reflects_degree g ρ hg hr a b target n p x hx

theorem bothSource_reflects (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (sourceL sourceR l r : R) (m : ℕ)
    (he : -g*l=l) (hl : l*l=ρ*l) (hk : r*r=ρ*r)
    (hleft : flipConstant g ρ a l=sourceL)
    (hright : flipConstant g ρ (signAt a b (2*m+1)) r=sourceR) (p : ℤ)
    (x : LinearMap.range (pairProjection sourceL sourceR (2*m)))
    (hx : TotalDegree (2*m+2) (p+1)
      ((bothSource g ρ hg hr a b sourceL sourceR l r m he hl hk hleft hright).map x).val) :
    TotalDegree (2*m) p x.val := by
  subst sourceL
  subst sourceR
  exact both_reflects_degree g ρ hg hr a b l r m p x hx

theorem bothSourceSize_reflects (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (sourceL sourceR l r : R) (m n : ℕ) (hlen : 2*m+2=n)
    (he : -g*l=l) (hl : l*l=ρ*l) (hk : r*r=ρ*r)
    (hleft : flipConstant g ρ a l=sourceL)
    (hright : flipConstant g ρ (signAt a b (2*m+1)) r=sourceR) (p : ℤ)
    (x : LinearMap.range (pairProjection sourceL sourceR (2*m)))
    (hx : TotalDegree n (p+1)
      ((bothSourceSize g ρ hg hr a b sourceL sourceR l r m n hlen he hl hk hleft hright).map x).val) :
    TotalDegree (2*m) p x.val := by
  subst n
  exact bothSource_reflects g ρ hg hr a b sourceL sourceR l r m he hl hk hleft hright p x hx

theorem z_closed_reflects (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (n : ℕ) (p : ℤ) (x : ZModule ρ n)
    (hx : TotalDegree (n+2) (p+1) (Verification.PathClosedZ.closedMap g ρ hg hr n x).val) :
    TotalDegree n p x.val :=
  rightSource_reflects g ρ hg hr true true (endpointConstant ρ n) (endpointConstant ρ (n+2)) n
    (endpointConstant_relation ρ (n+2)) (z_source_constant g ρ hr n) p x hx

theorem y_closed_reflects (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (m : ℕ) (p : ℤ) (x : YModule ρ m)
    (hx : TotalDegree (2*(m+1)) (p+1) (Verification.PathClosedY.closedMap g ρ hg hr m x).val) :
    TotalDegree (2*m) p x.val :=
  bothSourceSize_reflects g ρ hg hr false true 0 (endpointConstant ρ (2*m)) 0
    (endpointConstant ρ (2*(m+1))) m (2*(m+1)) (by omega)
    (by simp) (by simp) (endpointConstant_relation ρ (2*(m+1))) rfl
      (by simpa only [Nat.mul_add,Nat.mul_one] using y_source_right_constant g ρ hr m) p x hx

#print axioms rightSource_reflects
#print axioms bothSource_reflects
#print axioms bothSourceSize_reflects
#print axioms z_closed_reflects
#print axioms y_closed_reflects

end Verification.PathClosedReflectionTransport
