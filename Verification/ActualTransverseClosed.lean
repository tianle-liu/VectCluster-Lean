/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseLocalization
import Verification.ExchangeZeroFiber

/-!
# Actual Transverse Closed

The closed layer of the actual transverse chart is the actual affine
partner space over the character fiber. Successive coordinate quotients
are combined and the proved global chart isomorphism transports their ideal.
-/
noncomputable section
universe u
namespace Verification.ActualTransverseClosed
open Verification.ActualOpenChart Verification.ActualTransverseSlice
open Verification.ActualTransverseLocalization
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι)

def fullIdeal : Ideal (GlobalOpen R ι κ τ j B) := Ideal.span (Set.range (globalCoordinate R ι κ τ j B))
def lastIdeal : Ideal (GlobalOpen R ι κ τ j B) := Ideal.span {globalCoordinate R ι κ τ j B v}
abbrev FullClosed := GlobalOpen R ι κ τ j B ⧸ fullIdeal R ι κ τ j B

theorem partial_sup_last : partialIdeal R ι κ τ j B v ⊔ lastIdeal R ι κ τ j B v = fullIdeal R ι κ τ j B := by
  classical
  apply le_antisymm
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Ideal.subset_span (Set.mem_range_self i.1)
    · apply Ideal.span_le.mpr
      rintro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact Ideal.subset_span (Set.mem_range_self v)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : i = v
    · subst i
      exact (show lastIdeal R ι κ τ j B v ≤ partialIdeal R ι κ τ j B v ⊔ lastIdeal R ι κ τ j B v from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
    · exact (show partialIdeal R ι κ τ j B v ≤ partialIdeal R ι κ τ j B v ⊔ lastIdeal R ι κ τ j B v from le_sup_left) (Ideal.subset_span ⟨⟨i,hi⟩,rfl⟩)

theorem map_last : (lastIdeal R ι κ τ j B v).map (Ideal.Quotient.mkₐ R (partialIdeal R ι κ τ j B v)) =
    closedIdeal R ι κ τ j B v := by
  rw [lastIdeal,Ideal.map_span,Set.image_singleton]
  rfl

def closedToFull : ClosedSource R ι κ τ j B v ≃ₐ[R] FullClosed R ι κ τ j B :=
  (Ideal.quotientEquivAlgOfEq R (map_last R ι κ τ j B v).symm).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R (partialIdeal R ι κ τ j B v) (lastIdeal R ι κ τ j B v)).trans
      (Ideal.quotientEquivAlgOfEq R (partial_sup_last R ι κ τ j B v)))

theorem closedToFull_mk (z : GlobalOpen R ι κ τ j B) :
    closedToFull R ι κ τ j B v (Ideal.Quotient.mk (closedIdeal R ι κ τ j B v)
      (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) z)) =
    Ideal.Quotient.mk (fullIdeal R ι κ τ j B) z := by
  dsimp only [closedToFull,AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  change Ideal.quotientEquivAlgOfEq R _
    (DoubleQuot.quotQuotEquivQuotSup (partialIdeal R ι κ τ j B v) (lastIdeal R ι κ τ j B v)
      (DoubleQuot.quotQuotMk (partialIdeal R ι κ τ j B v) (lastIdeal R ι κ τ j B v) z)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk,Ideal.quotientEquivAlgOfEq_mk]

variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0)
include hB

theorem map_full : (fullIdeal R ι κ τ j B).map (globalOpenEquiv R ι κ τ j B hB).toRingHom =
    ExchangeZeroFiber.zeroIdeal (characters R ι κ τ B) := by
  rw [fullIdeal,Ideal.map_span,← Set.range_comp,ExchangeZeroFiber.zeroIdeal]
  apply congrArg Ideal.span
  apply congrArg Set.range
  exact funext (globalOpenEquiv_coordinate R ι κ τ j B hB)

def fullToLocal : FullClosed R ι κ τ j B ≃ₐ[R] ExchangeZeroFiber.Closed (characters R ι κ τ B) :=
  Ideal.quotientEquivAlg _ _ (globalOpenEquiv R ι κ τ j B hB) (map_full R ι κ τ j B hB).symm

theorem fullToLocal_mk (z : GlobalOpen R ι κ τ j B) :
    fullToLocal R ι κ τ j B hB (Ideal.Quotient.mk (fullIdeal R ι κ τ j B) z) =
      ExchangeZeroFiber.quotient (R := R) (characters R ι κ τ B) (globalOpenEquiv R ι κ τ j B hB z) := rfl

def affineEquiv : ClosedSource R ι κ τ j B v ≃ₐ[R] ExchangeZeroFiber.Affine (characters R ι κ τ B) :=
  (closedToFull R ι κ τ j B v).trans ((fullToLocal R ι κ τ j B hB).trans
    (ExchangeZeroFiber.affineEquiv (R := R) (characters R ι κ τ B)))

theorem affineEquiv_mk (z : GlobalOpen R ι κ τ j B) :
    affineEquiv R ι κ τ j B v hB (Ideal.Quotient.mk (closedIdeal R ι κ τ j B v)
      (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) z)) =
      ExchangeZeroFiber.affineEquiv (R := R) (characters R ι κ τ B)
        (ExchangeZeroFiber.quotient (R := R) (characters R ι κ τ B) (globalOpenEquiv R ι κ τ j B hB z)) := by
  dsimp only [affineEquiv,AlgEquiv.trans_apply]
  rw [closedToFull_mk,fullToLocal_mk]

#print axioms fullIdeal
#print axioms lastIdeal
#print axioms FullClosed
#print axioms partial_sup_last
#print axioms map_last
#print axioms closedToFull
#print axioms closedToFull_mk
#print axioms map_full
#print axioms fullToLocal
#print axioms fullToLocal_mk
#print axioms affineEquiv
#print axioms affineEquiv_mk
end Verification.ActualTransverseClosed
