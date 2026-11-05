/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointRecursionConstants
import Verification.PathBothClosedRecursion

/-!
# Path Endpoint Closed Data

Bundled closed recursion data permits endpoint parameter transport
without unfolding the actual quotient maps during dependent type comparison.
-/

namespace Verification.PathEndpointClosedData

open Classical Verification.PathCochains Verification.PathEndpointTotal
  Verification.PathEndpointComplex Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathClosedEmbedding Verification.PathBothClosedRecursion

variable {R : Type*} [CommRing R]

structure ClosedData {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (D : M →ₗ[R] M) (E : N →ₗ[R] N) (C : Submodule R N) where
  map : M →ₗ[R] N
  injective : Function.Injective map
  range_iff : ∀ x, x ∈ LinearMap.range map ↔ x ∈ C
  intertwining : E.comp map=map.comp D

noncomputable def firstSupport (n : ℕ) : Submodule R (Total (R := R) n) where
  carrier := {x | ∀ I, 1 ∉ I.val → x I=0}
  zero_mem' := by
    change ∀ I : Config n, 1 ∉ I.val → (0 : Total (R := R) n) I=0
    intro I _
    rfl
  add_mem' := by intro x y hx hy I hI; simp only [Pi.add_apply,hx I hI,hy I hI,add_zero]
  smul_mem' := by intro r x hx I hI; simp only [Pi.smul_apply,hx I hI,smul_zero]

theorem firstSupport_closed (n : ℕ) : firstSupport (R := R) (n+2)=closedSupport n := by
  ext x
  exact (mem_closedSupport n x).symm

noncomputable def rightSupport (k : R) (n : ℕ) : Submodule R (LinearMap.range (right k n)) :=
  (firstSupport n).comap (LinearMap.range (right k n)).subtype

noncomputable def bothSupport (l r : R) (n : ℕ) : Submodule R (LinearMap.range (pairProjection l r n)) :=
  (firstSupport n).comap (LinearMap.range (pairProjection l r n)).subtype

noncomputable def rightData (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (k : R) (n : ℕ) (hk : k*k=ρ*k) :
    ClosedData (R := R)
      (M := LinearMap.range (right (flipConstant g ρ (signAt a b (n+1)) k) n))
      (N := LinearMap.range (right k (n+2)))
      (imageDifferential (right (flipConstant g ρ (signAt a b (n+1)) k) n) (differential g ρ n))
      (imageDifferential (right k (n+2)) (differential g ρ (n+2))) (rightSupport k (n+2)) where
  map := Verification.PathRightClosedRecursion.closedMap g ρ hg hr a b k n
  injective := Verification.PathRightClosedRecursion.closedMap_injective g ρ hg hr a b k n
  range_iff x := by
    change x ∈ LinearMap.range (Verification.PathRightClosedRecursion.closedMap g ρ hg hr a b k n) ↔
      x.val ∈ firstSupport (n+2)
    rw [firstSupport_closed]
    exact Verification.PathRightClosedRecursion.closedMap_range g ρ hg hr a b k n x
  intertwining := Verification.PathRightClosedRecursion.closedMap_differential g ρ hg hr a b k n hk

noncomputable def bothData (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (l r : R) (m : ℕ) (he : -g*l=l) (hl : l*l=ρ*l) (hk : r*r=ρ*r) :
    ClosedData (R := R)
      (M := LinearMap.range (pairProjection (flipConstant g ρ a l)
        (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m)))
      (N := LinearMap.range (pairProjection l r (2*m+2)))
      (imageDifferential (pairProjection (flipConstant g ρ a l)
      (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m)) (differential g ρ (2*m)))
        (imageDifferential (pairProjection l r (2*m+2)) (differential g ρ (2*m+2)))
          (bothSupport l r (2*m+2)) where
  map := Verification.PathBothClosedRecursion.closedMap g ρ hg hr a b l r m
  injective := Verification.PathBothClosedRecursion.closedMap_injective g ρ hg hr a b l r m
  range_iff x := by
    change x ∈ LinearMap.range (Verification.PathBothClosedRecursion.closedMap g ρ hg hr a b l r m) ↔
      x.val ∈ firstSupport (2*m+2)
    rw [firstSupport_closed]
    exact Verification.PathBothClosedRecursion.closedMap_range g ρ hg hr a b l r m x
  intertwining := Verification.PathBothClosedRecursion.closedMap_differential g ρ hg hr a b l r m he hl hk

#print axioms ClosedData
#print axioms firstSupport
#print axioms firstSupport_closed
#print axioms rightSupport
#print axioms bothSupport
#print axioms rightData
#print axioms bothData

end Verification.PathEndpointClosedData
