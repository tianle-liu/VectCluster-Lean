/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCokernel
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Path Weight Basis

Canonical weight-labelled bases, including literal quotient representatives
and the exact finite ranks in the path first-boundary computation.
-/

namespace Verification.PathWeightBasis

open Verification.PathWords Verification.PathFirstBoundary Verification.PathCokernel

/-- The Y survivors are precisely weights 0,2,...,2a. -/
def yWeightEquiv (a : ℕ) : Weight true (2*a) ≃ Fin (a+1) where
  toFun k := ⟨k.val.val/2, by have hk := k.val.isLt; omega⟩
  invFun k := ⟨⟨2*k.val, by have hk := k.isLt; omega⟩, by intro _; change (2*k.val) % 2=0; omega⟩
  left_inv k := by
    apply Subtype.ext
    apply Fin.ext
    have hk := k.property rfl
    simp only
    omega
  right_inv k := by apply Fin.ext; simp

/-- The Z word has one frozen plus n mutable positions, hence weights 0 through n+1. -/
def zWeightEquiv (n : ℕ) : Weight false (n+1) ≃ Fin (n+2) where
  toFun k := k.val
  invFun k := ⟨k, by intro h; cases h⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {R : Type*} [CommRing R] (m : Bool) (n : ℕ) (heven : m=true → n % 2=0)

theorem cokernelEquiv_mk (x : Word n →₀ R) :
    cokernelEquiv m n heven ((LinearMap.range (firstBoundary m n)).mkQ x)=
      projection (R := R) m n x := rfl

/-- No freeness is assumed: this basis is transported through the proved actual cokernel map. -/
noncomputable def weightBasis : Basis (Weight m n) R (Cokernel (R := R) m n) :=
  Finsupp.basisSingleOne.map (cokernelEquiv m n heven).symm

theorem weightBasis_apply (k : Weight m n) :
    weightBasis (R := R) m n heven k=
      (LinearMap.range (firstBoundary m n)).mkQ (Finsupp.single (representative k) 1) := by
  apply (cokernelEquiv (R := R) m n heven).injective
  simp only [weightBasis, Basis.map_apply, Finsupp.coe_basisSingleOne,
    LinearEquiv.apply_symm_apply, cokernelEquiv_mk, projection_single, projectionColumn,
    dif_pos (representative_good k), representative_weight]

/-- The manuscript's exact rank-a+1 all-mutable presentation. -/
noncomputable def yBasis (a : ℕ) : Basis (Fin (a+1)) R (Cokernel (R := R) true (2*a)) :=
  (weightBasis true (2*a) (by intro _; omega)).reindex (yWeightEquiv a)

/-- The manuscript's exact rank-n+2 initially frozen presentation. -/
noncomputable def zBasis (n : ℕ) : Basis (Fin (n+2)) R (Cokernel (R := R) false (n+1)) :=
  (weightBasis false (n+1) (by intro h; cases h)).reindex (zWeightEquiv n)

theorem y_finrank [Nontrivial R] (a : ℕ) : Module.finrank R (Cokernel (R := R) true (2*a))=a+1 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (yBasis (R := R) a)

theorem z_finrank [Nontrivial R] (n : ℕ) : Module.finrank R (Cokernel (R := R) false (n+1))=n+2 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (zBasis (R := R) n)

#print axioms yWeightEquiv
#print axioms zWeightEquiv
#print axioms cokernelEquiv_mk
#print axioms weightBasis
#print axioms weightBasis_apply
#print axioms yBasis
#print axioms zBasis
#print axioms y_finrank
#print axioms z_finrank

end Verification.PathWeightBasis
