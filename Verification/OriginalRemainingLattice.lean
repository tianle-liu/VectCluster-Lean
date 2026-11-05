/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalFreeCoordinateData
import Verification.TameComplementaryCharacterLattice

/-!
# Original Remaining Lattice

The remaining columns in the named-coordinate splitting satisfy
the original rank and tame Smith conditions.
-/
noncomputable section
namespace Verification.OriginalRemainingLattice
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
open Verification.ComplementaryCharacterLattice
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def remainingMap : (Selected n I→₀ℤ) →ₗ[ℤ] (RemainingIndex κ n I B→₀ℤ) :=
  remaining (splitting κ n I B) (GlobalExchangeSmooth.selectedMap κ n B I)

theorem selected_free_zero (p : Selected n I→₀ℤ) :
    (splitting κ n I B (GlobalExchangeSmooth.selectedMap κ n B I p)).1=0 := by
  have h : (LinearMap.fst ℤ (FreeIndex κ n I B→₀ℤ) (RemainingIndex κ n I B→₀ℤ)).comp
      ((splitting κ n I B).toLinearMap.comp (GlobalExchangeSmooth.selectedMap κ n B I))=0 := by
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext_ring
    change (splitting κ n I B (GlobalExchangeSmooth.selectedMap κ n B I (Finsupp.single i 1))).1=0
    simp only [GlobalExchangeSmooth.selectedMap,ActualOpenGeometry.columnMap_single]
    exact columns_free_zero κ n I B i
  exact LinearMap.congr_fun h p

theorem remaining_injective (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I)) :
    Function.Injective (remainingMap κ n I B) :=
  injective (splitting κ n I B) _ (selected_free_zero κ n I B) hf

theorem remaining_saturated
    (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))) :
    FreezingLattice.Saturated (LinearMap.range (remainingMap κ n I B)) :=
  saturated (splitting κ n I B) _ (selected_free_zero κ n I B) hs

theorem remaining_tame (R : Type) [CommRing R]
    (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I)) {m l : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I⊕κ) m)
    (t : Basis.SmithNormalForm (LinearMap.range (remainingMap κ n I B)) (RemainingIndex κ n I B) l)
    (he : ∀ i,IsUnit ((s.a i).natAbs:R)) : ∀ i,IsUnit ((t.a i).natAbs:R) :=
  TameComplementaryCharacterLattice.remaining_tame _ hf s
    (splitting κ n I B) (selected_free_zero κ n I B) R t he

#print axioms remainingMap
#print axioms selected_free_zero
#print axioms remaining_injective
#print axioms remaining_saturated
#print axioms remaining_tame
end Verification.OriginalRemainingLattice
