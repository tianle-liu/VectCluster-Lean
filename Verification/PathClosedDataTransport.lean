/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointClosedData

/-!
# Path Closed Data Transport

Equality transport is proved with free scalar and size parameters, before
specializing endpoint expressions, to avoid unfolding quotient projectors.
-/

namespace Verification.PathClosedDataTransport

open Verification.PathCochains Verification.PathEndpointTotal Verification.PathEndpointComplex
  Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathBothClosedRecursion Verification.PathEndpointClosedData

variable {R : Type*} [CommRing R]

noncomputable def rightSource (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (source target : R) (n : ℕ) (hk : target*target=ρ*target)
    (he : flipConstant g ρ (signAt a b (n+1)) target=source) :
    ClosedData (R := R) (M := LinearMap.range (right source n))
      (N := LinearMap.range (right target (n+2)))
      (imageDifferential (right source n) (differential g ρ n))
      (imageDifferential (right target (n+2)) (differential g ρ (n+2))) (rightSupport target (n+2)) := by
  subst source
  exact rightData g ρ hg hr a b target n hk

noncomputable def bothSource (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (sourceL sourceR l r : R) (m : ℕ)
    (he : -g*l=l) (hl : l*l=ρ*l) (hk : r*r=ρ*r)
    (hleft : flipConstant g ρ a l=sourceL)
    (hright : flipConstant g ρ (signAt a b (2*m+1)) r=sourceR) :
    ClosedData (R := R) (M := LinearMap.range (pairProjection sourceL sourceR (2*m)))
      (N := LinearMap.range (pairProjection l r (2*m+2)))
      (imageDifferential (pairProjection sourceL sourceR (2*m)) (differential g ρ (2*m)))
      (imageDifferential (pairProjection l r (2*m+2)) (differential g ρ (2*m+2)))
        (bothSupport l r (2*m+2)) := by
  subst sourceL
  subst sourceR
  exact bothData g ρ hg hr a b l r m he hl hk

noncomputable def bothSourceSize (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (sourceL sourceR l r : R) (m n : ℕ) (hlen : 2*m+2=n)
    (he : -g*l=l) (hl : l*l=ρ*l) (hk : r*r=ρ*r)
    (hleft : flipConstant g ρ a l=sourceL)
    (hright : flipConstant g ρ (signAt a b (2*m+1)) r=sourceR) :
    ClosedData (R := R) (M := LinearMap.range (pairProjection sourceL sourceR (2*m)))
      (N := LinearMap.range (pairProjection l r n))
      (imageDifferential (pairProjection sourceL sourceR (2*m)) (differential g ρ (2*m)))
      (imageDifferential (pairProjection l r n) (differential g ρ n)) (bothSupport l r n) := by
  subst n
  exact bothSource g ρ hg hr a b sourceL sourceR l r m he hl hk hleft hright

#print axioms rightSource
#print axioms bothSource
#print axioms bothSourceSize

end Verification.PathClosedDataTransport
