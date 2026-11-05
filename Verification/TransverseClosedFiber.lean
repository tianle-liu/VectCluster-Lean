/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseNormalMap
import Verification.PrincipalPairMaps
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Transverse Closed Fiber

The principal quotient u=0 is identified with the actual new torus
fiber, and the canonical quotient map of principal pairs becomes the
previously constructed actual closed-slice map.
-/
noncomputable section
namespace Verification.TransverseClosedFiber
open Verification.ActualOpenChart Verification.ActualTransverseSlice
open Verification.ActualTransverseLocalization Verification.ExchangeTransverseSlice
open Verification.ActualTransverseNormalMap
universe u
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)

def fiberEquiv : SliceClosed R ι κ τ B ≃ₐ[R] Fiber (characters R ι κ τ B) :=
  ((Ideal.quotientEquivAlgOfEq (Fiber (characters R ι κ τ B))
    (show parameterIdeal (characters R ι κ τ B) =
      Ideal.span {Polynomial.X - Polynomial.C (0 : Fiber (characters R ι κ τ B))} by
      simp only [map_zero, sub_zero]; rfl)).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (0 : Fiber (characters R ι κ τ B)))).restrictScalars R

omit [Fintype ι] in
theorem fiberEquiv_mk (p : Slice (characters R ι κ τ B)) :
    fiberEquiv R ι κ τ B (Ideal.Quotient.mk (parameterIdeal (characters R ι κ τ B)) p) =
      Polynomial.eval 0 p := by
  dsimp only [fiberEquiv, AlgEquiv.restrictScalars_apply, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk, Polynomial.quotientSpanXSubCAlgEquiv_mk]

def principalClosedMap : ClosedSource R ι κ τ j B v →ₐ[R] SliceClosed R ι κ τ B :=
  PrincipalPairMaps.closedMap R (Intermediate R ι κ τ j B v) (Slice (characters R ι κ τ B))
    (originalParameter R ι κ τ j B v) Polynomial.X
    (transverseSlice R ι κ τ j B hB v) (transverse_parameter R ι κ τ j B hB v)

theorem principalClosedMap_mk (z : Intermediate R ι κ τ j B v) :
    principalClosedMap R ι κ τ j B hB v (Ideal.Quotient.mk (closedIdeal R ι κ τ j B v) z) =
      Ideal.Quotient.mk (parameterIdeal (characters R ι κ τ B))
        (transverseSlice R ι κ τ j B hB v z) := rfl

theorem closedMap_fiber : (fiberEquiv R ι κ τ B).toAlgHom.comp
    (principalClosedMap R ι κ τ j B hB v) = closedSlice R ι κ τ j B hB v := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro z
  change fiberEquiv R ι κ τ B
    (principalClosedMap R ι κ τ j B hB v (Ideal.Quotient.mk (closedIdeal R ι κ τ j B v) z)) =
      closedSlice R ι κ τ j B hB v (Ideal.Quotient.mk (closedIdeal R ι κ τ j B v) z)
  rw [principalClosedMap_mk, fiberEquiv_mk, closedSlice_coefficient]
  rfl

#print axioms fiberEquiv
#print axioms fiberEquiv_mk
#print axioms principalClosedMap
#print axioms principalClosedMap_mk
#print axioms closedMap_fiber
end Verification.TransverseClosedFiber
