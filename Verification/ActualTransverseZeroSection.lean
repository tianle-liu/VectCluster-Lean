/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseClosed
import Verification.ExchangeZeroEvaluation

/-!
# Actual Transverse Zero Section

Through the actual closed-layer isomorphism, the closed transverse map
is exactly the zero section of affine partner space. Its retraction and
the explicit affine contraction are therefore available for A1 comparison.
-/
noncomputable section
universe u
namespace Verification.ActualTransverseZeroSection
open Verification.ActualOpenChart Verification.ActualTransverseSlice
open Verification.ActualTransverseLocalization Verification.ActualTransverseClosed
open Verification.ExchangeTransverseSlice
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)

theorem closedSlice_zeroSection : closedSlice R ι κ τ j B hB v =
    (ExchangeZeroEvaluation.zeroSection (R := R) (characters R ι κ τ B)).comp
      (affineEquiv R ι κ τ j B v hB).toAlgHom := by
  apply AlgHom.ext
  intro z
  obtain ⟨w,rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective w
  change closedSlice R ι κ τ j B hB v (Ideal.Quotient.mk (closedIdeal R ι κ τ j B v)
    (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) z)) =
    ExchangeZeroEvaluation.zeroSection (R := R) (characters R ι κ τ B)
      (affineEquiv R ι κ τ j B v hB (Ideal.Quotient.mk (closedIdeal R ι κ τ j B v)
        (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) z)))
  rw [affineEquiv_mk]
  exact (ExchangeZeroEvaluation.zeroSection_equiv_apply (R := R) (characters R ι κ τ B) v
    (globalOpenEquiv R ι κ τ j B hB z)).symm

def structureMap : Fiber (characters R ι κ τ B) →ₐ[R] ClosedSource R ι κ τ j B v :=
  (affineEquiv R ι κ τ j B v hB).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R (Fiber (characters R ι κ τ B)) (ExchangeZeroFiber.Affine (characters R ι κ τ B)))

theorem closedSlice_structureMap : (closedSlice R ι κ τ j B hB v).comp
    (structureMap R ι κ τ j B hB v) = AlgHom.id R (Fiber (characters R ι κ τ B)) := by
  apply AlgHom.ext
  intro z
  rw [closedSlice_zeroSection]
  change ExchangeZeroEvaluation.zeroSection (R := R) (characters R ι κ τ B)
    (affineEquiv R ι κ τ j B v hB ((affineEquiv R ι κ τ j B v hB).symm (MvPolynomial.C z))) = z
  rw [AlgEquiv.apply_symm_apply]
  exact MvPolynomial.aeval_C _ _

theorem closedSlice_after_affine :
    (closedSlice R ι κ τ j B hB v).comp (affineEquiv R ι κ τ j B v hB).symm.toAlgHom =
      ExchangeZeroEvaluation.zeroSection (R := R) (characters R ι κ τ B) := by
  apply AlgHom.ext
  intro z
  rw [closedSlice_zeroSection]
  change ExchangeZeroEvaluation.zeroSection (R := R) (characters R ι κ τ B)
    (affineEquiv R ι κ τ j B v hB ((affineEquiv R ι κ τ j B v hB).symm z)) = _
  rw [AlgEquiv.apply_symm_apply]

#print axioms closedSlice_zeroSection
#print axioms structureMap
#print axioms closedSlice_structureMap
#print axioms closedSlice_after_affine
end Verification.ActualTransverseZeroSection
