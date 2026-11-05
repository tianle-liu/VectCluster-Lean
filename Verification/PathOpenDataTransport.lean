/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenRecursion

/-!
# Path Open Data Transport

Parameter transport is proved before specializing large endpoint-image
modules, preserving the actual maps and exact closed-support kernels.
-/

namespace Verification.PathOpenDataTransport

open Verification.PathCochains Verification.PathEndpointTotal Verification.PathEndpointComplex
  Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathEndpointClosedData Verification.PathOpenBoth Verification.PathOpenData
  Verification.PathOpenRecursion

variable {R : Type*} [CommRing R]

noncomputable def rightTarget (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n : ℕ) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) :
    OpenData (R := R) (M := LinearMap.range (right source (n+1)))
      (N := Bool → LinearMap.range (right target n))
      (imageDifferential (right source (n+1)) (differential g ρ (n+1)))
      (torusDifferential g ρ target n) (rightSupport source (n+1)) := by
  subst target
  exact Verification.PathOpenRecursion.rightData g ρ hg hr a b source n hk

noncomputable def bothTarget (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n : ℕ) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) :
    OpenData (R := R) (M := LinearMap.range (bothProjection source (n+1)))
      (N := LinearMap.range (right target n))
      (imageDifferential (bothProjection source (n+1)) (differential g ρ (n+1)))
      (imageDifferential (right target n) (differential g ρ n))
      (bothSupport 0 source (n+1)) := by
  subst target
  exact Verification.PathOpenRecursion.bothData g ρ hg hr a b source n hk

noncomputable def bothTargetSize (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n m : ℕ) (hm : n+1=m) (hk : source*source=ρ*source)
    (h : flipConstant g ρ (signAt a b (n+1)) source=target) :
    OpenData (R := R) (M := LinearMap.range (bothProjection source m))
      (N := LinearMap.range (right target n))
      (imageDifferential (bothProjection source m) (differential g ρ m))
      (imageDifferential (right target n) (differential g ρ n))
      (bothSupport 0 source m) := by
  subst m
  exact bothTarget g ρ hg hr a b source target n hk h

#print axioms rightTarget
#print axioms bothTarget
#print axioms bothTargetSize

end Verification.PathOpenDataTransport
