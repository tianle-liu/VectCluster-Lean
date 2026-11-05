/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittCharacterSplitting
import Verification.BinarySignedFiberCoordinates
import Verification.OriginalWittStratumFree

/-!
# Original Witt Coordinate Quotient

The literal signed quotient in the original coordinates is identified
with the torus basis using the actual geometric integral splitting.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 15000
open scoped Classical
namespace Verification.OriginalWittCoordinateQuotient
open Verification.OriginalWittQuotient Verification.OriginalWittRelationRank
open Verification.OriginalWittCharacterSplitting Verification.OriginalWittStratumFree
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (hz : ∀ i j : I, B (Sum.inl j.val) (Sum.inl i.val)=0)

def equiv : Stratum (fun a v => B a (Sum.inl v)) I ≃ₐ[ℤ]
    MonoidAlgebra ℤ (Multiplicative (Fin (ExplicitStratumTorus.torusRank κ n I B) → ZMod 2)) :=
  BinarySignedFiberCoordinates.quotientEquiv
    (relationMap (fun a v => B a (Sum.inl v)) I) (signs I)
    (splitting κ n I B hf hs) (splitting_relation κ n I B hf hs hz) _
    (ideal_eq (fun a v => B a (Sum.inl v)) I)

#print axioms equiv

theorem monomial (m : Bits (Fin n) κ) :
    equiv κ n I B hf hs hz (Ideal.Quotient.mk _
      (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m))) =
      algebraMap ℤ _ (BinarySignedFiber.character (signs I)
        (Multiplicative.ofAdd (splitting κ n I B hf hs m).1) : ℤ) *
        MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd (splitting κ n I B hf hs m).2) := by
  exact BinarySignedFiberCoordinates.quotientEquiv_monomial _ _ _ _ _ _ _

#print axioms monomial
end Verification.OriginalWittCoordinateQuotient
