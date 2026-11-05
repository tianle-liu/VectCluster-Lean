/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignNormalization

/-!
# Path Signed Cokernel

Complete cokernel and basis comparison for the unspecialized g-boundary.
There is no specialization to g=1 or to a field.
-/

namespace Verification.PathSignedCokernel

open Verification.PathWords Verification.PathFirstBoundary Verification.PathCokernel
  Verification.PathWeightBasis Verification.PathSignNormalization

variable {R : Type*} [CommRing R] (g : R) (hg : g*g=1) (m : Bool) (n : ℕ)

/-- The actual diagonal equivalence carries exactly the full image submodule. -/
theorem range_normalization :
    (LinearMap.range (signedBoundary g m n)).map (wordEquiv g hg n).toLinearMap=
      LinearMap.range (firstBoundary m n) := by
  ext x
  constructor
  · rintro ⟨_,⟨y,rfl⟩,rfl⟩
    refine ⟨sourceEquiv g hg m n y, ?_⟩
    exact (congrArg (fun f : _ →ₗ[R] _ => f y) (boundary_intertwining g hg m n)).symm
  · rintro ⟨y,rfl⟩
    refine ⟨signedBoundary g m n ((sourceEquiv g hg m n).symm y), ⟨_,rfl⟩, ?_⟩
    have hh := congrArg (fun f : _ →ₗ[R] _ => f ((sourceEquiv g hg m n).symm y))
      (boundary_intertwining g hg m n)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hh

abbrev SignedCokernel := (Word n →₀ R) ⧸ LinearMap.range (signedBoundary g m n)

/-- Full original g-dependent first-boundary cokernel, in its actual allowed weights. -/
noncomputable def signedCokernelEquiv (heven : m=true → n % 2=0) :
    SignedCokernel g m n ≃ₗ[R] (Weight m n →₀ R) :=
  (Submodule.Quotient.equiv _ _ (wordEquiv g hg n) (range_normalization g hg m n)).trans
    (cokernelEquiv m n heven)

/-- Every surviving weight has a genuine basis vector over any commutative ring. -/
noncomputable def signedWeightBasis (heven : m=true → n % 2=0) :
    Basis (Weight m n) R (SignedCokernel g m n) :=
  Finsupp.basisSingleOne.map (signedCokernelEquiv g hg m n heven).symm

/-- The quotient coordinates are the literal positional sign change followed by the proved projection. -/
theorem signedCokernelEquiv_mk (heven : m=true → n % 2=0) (x : Word n →₀ R) :
    signedCokernelEquiv g hg m n heven ((LinearMap.range (signedBoundary g m n)).mkQ x)=
      projection m n (wordEquiv g hg n x) := rfl

noncomputable def signedYBasis (a : ℕ) :
    Basis (Fin (a+1)) R (SignedCokernel g true (2*a)) :=
  (signedWeightBasis g hg true (2*a) (by intro _; omega)).reindex (yWeightEquiv a)

noncomputable def signedZBasis (n : ℕ) :
    Basis (Fin (n+2)) R (SignedCokernel g false (n+1)) :=
  (signedWeightBasis g hg false (n+1) (by intro h; cases h)).reindex (zWeightEquiv n)

include hg in
theorem signedY_finrank [Nontrivial R] (a : ℕ) :
    Module.finrank R (SignedCokernel g true (2*a))=a+1 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (signedYBasis g hg a)

include hg in
theorem signedZ_finrank [Nontrivial R] (n : ℕ) :
    Module.finrank R (SignedCokernel g false (n+1))=n+2 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (signedZBasis g hg n)

#print axioms range_normalization
#print axioms SignedCokernel
#print axioms signedCokernelEquiv
#print axioms signedWeightBasis
#print axioms signedCokernelEquiv_mk
#print axioms signedYBasis
#print axioms signedZBasis
#print axioms signedY_finrank
#print axioms signedZ_finrank

end Verification.PathSignedCokernel
