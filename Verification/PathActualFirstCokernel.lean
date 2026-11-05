/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualColumnRelations

/-!
# Path Actual First Cokernel

The actual Y/Z rho-zero first-boundary cutouts have precisely the
original signed kill/slide cokernels, hence the manuscript's stated bases.
-/

namespace Verification.PathActualFirstCokernel

open Verification.PathWords Verification.PathFirstBoundaryCutout Verification.PathSignNormalization
  Verification.PathSignedCokernel Verification.PathCokernel Verification.PathFirstRangeInclusion
  Verification.PathActualColumnRelations

variable {R : Type*} [CommRing R]

theorem z_range_eq (g : R) (hg : g*g=1) (n : ℕ) :
    LinearMap.range (zBoundary g n)=LinearMap.range (signedBoundary g false (n+1)) := by
  apply le_antisymm
  · rw [zBoundary,Finsupp.range_linearCombination]
    apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    exact zColumn_mem_signed g hg n s
  · exact z_signed_range_le g hg n

theorem y_range_eq (g : R) (hg : g*g=1) (a : ℕ) :
    LinearMap.range (yBoundary g a)=LinearMap.range (signedBoundary g true (2*a)) := by
  apply le_antisymm
  · rw [yBoundary,Finsupp.range_linearCombination]
    apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    exact yColumn_mem_signed g hg a s
  · exact y_signed_range_le g hg a

abbrev ZCokernel (g : R) (n : ℕ) := (Word (n+1) →₀ R) ⧸ LinearMap.range (zBoundary g n)
abbrev YCokernel (g : R) (a : ℕ) := (Word (2*a) →₀ R) ⧸ LinearMap.range (yBoundary g a)

noncomputable def zSignedEquiv (g : R) (hg : g*g=1) (n : ℕ) :
    ZCokernel g n ≃ₗ[R] SignedCokernel g false (n+1) :=
  Submodule.quotEquivOfEq _ _ (z_range_eq g hg n)

noncomputable def ySignedEquiv (g : R) (hg : g*g=1) (a : ℕ) :
    YCokernel g a ≃ₗ[R] SignedCokernel g true (2*a) :=
  Submodule.quotEquivOfEq _ _ (y_range_eq g hg a)

/-- The actual first boundary has one free survivor in every Z weight 0,...,n+1. -/
noncomputable def zWeightEquiv (g : R) (hg : g*g=1) (n : ℕ) :
    ZCokernel g n ≃ₗ[R] (Weight false (n+1) →₀ R) :=
  (zSignedEquiv g hg n).trans (signedCokernelEquiv g hg false (n+1) (by intro h; cases h))

/-- The actual first boundary has one free survivor in every even Y weight 0,...,2a. -/
noncomputable def yWeightEquiv (g : R) (hg : g*g=1) (a : ℕ) :
    YCokernel g a ≃ₗ[R] (Weight true (2*a) →₀ R) :=
  (ySignedEquiv g hg a).trans (signedCokernelEquiv g hg true (2*a) (by intro _; omega))

noncomputable def zBasis (g : R) (hg : g*g=1) (n : ℕ) : Basis (Fin (n+2)) R (ZCokernel g n) :=
  (signedZBasis g hg n).map (zSignedEquiv g hg n).symm

noncomputable def yBasis (g : R) (hg : g*g=1) (a : ℕ) : Basis (Fin (a+1)) R (YCokernel g a) :=
  (signedYBasis g hg a).map (ySignedEquiv g hg a).symm

theorem z_finrank [Nontrivial R] (g : R) (hg : g*g=1) (n : ℕ) :
    Module.finrank R (ZCokernel g n)=n+2 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (zBasis g hg n)

theorem y_finrank [Nontrivial R] (g : R) (hg : g*g=1) (a : ℕ) :
    Module.finrank R (YCokernel g a)=a+1 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (yBasis g hg a)

#print axioms z_range_eq
#print axioms y_range_eq
#print axioms ZCokernel
#print axioms YCokernel
#print axioms zSignedEquiv
#print axioms ySignedEquiv
#print axioms zWeightEquiv
#print axioms yWeightEquiv
#print axioms zBasis
#print axioms yBasis
#print axioms z_finrank
#print axioms y_finrank

end Verification.PathActualFirstCokernel
