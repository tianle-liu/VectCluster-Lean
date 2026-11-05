/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveTorusRank
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

/-!
# Primitive Sign Fiber

Boolean character fibers of an actual primitive column lattice.
The affine fiber coordinates and their size are derived from saturation.
-/
noncomputable section
namespace Verification.PrimitiveSignFiber
variable {M P Q : Type*} [AddCommGroup M] [AddCommGroup P] [AddCommGroup Q]
abbrev Bit := ZMod 2

def fiber (f : P →ₗ[ℤ] M) (c : P →ₗ[ℤ] Bit) :=
  {φ : M →ₗ[ℤ] Bit // φ.comp f=c}

def fiberEquiv (f : P →ₗ[ℤ] M) (c : P →ₗ[ℤ] Bit)
    (e : M ≃ₗ[ℤ] (P × Q)) (he : ∀ p, e (f p)=(p,0)) :
    fiber f c ≃ (Q →ₗ[ℤ] Bit) where
  toFun φ := φ.val.comp (e.symm.toLinearMap.comp (LinearMap.inr ℤ P Q))
  invFun ψ := ⟨(c.coprod ψ).comp e.toLinearMap,by
    apply LinearMap.ext
    intro p
    simp [he]⟩
  left_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    have hφ (p : P) : φ.val (f p)=c p := LinearMap.congr_fun φ.property p
    have hm : m=f (e m).1 + e.symm (0,(e m).2) := by
      apply e.injective
      simp [he]
    change c (e m).1 + φ.val (e.symm (0,(e m).2))=φ.val m
    conv_rhs => rw [hm,map_add,hφ]
  right_inv ψ := by
    apply LinearMap.ext
    intro q
    simp

variable [Module.Finite ℤ M]

def primitiveEquiv (f : P →ₗ[ℤ] M) (c : P →ₗ[ℤ] Bit)
    (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    fiber f c ≃ ((M ⧸ LinearMap.range f) →ₗ[ℤ] Bit) := by
  let h := Verification.PrimitiveLattice.primitive_columns_split_compatible f hf hs
  exact fiberEquiv f c h.choose h.choose_spec

def coordinates (f : P →ₗ[ℤ] M) (c : P →ₗ[ℤ] Bit)
    (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    fiber f c ≃ (Fin (Module.finrank ℤ (M ⧸ LinearMap.range f)) → Bit) := by
  letI := Verification.PrimitiveLattice.quotient_free (LinearMap.range f) hs
  exact (primitiveEquiv f c hf hs).trans
    ((Module.finBasis ℤ (M ⧸ LinearMap.range f)).constr ℤ).symm.toEquiv

theorem fiber_card (f : P →ₗ[ℤ] M) (c : P →ₗ[ℤ] Bit)
    (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Nat.card (fiber f c)=2 ^ Module.finrank ℤ (M ⧸ LinearMap.range f) := by
  rw [Nat.card_congr (coordinates f c hf hs)]
  simp [Nat.card_eq_fintype_card,Bit]

theorem fiber_nonempty (f : P →ₗ[ℤ] M) (c : P →ₗ[ℤ] Bit)
    (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Nonempty (fiber f c) := ⟨(coordinates f c hf hs).symm 0⟩

#print axioms fiber
#print axioms fiberEquiv
#print axioms primitiveEquiv
#print axioms coordinates
#print axioms fiber_card
#print axioms fiber_nonempty
end Verification.PrimitiveSignFiber

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.PrimitiveSignFiber.Bit
