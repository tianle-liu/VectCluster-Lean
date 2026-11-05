/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExplicitStratumCoordinates

/-!
# Original Zero Layer Cast

Reindexing an actual zero layer by an equality of its selected vertex sets
retains every literal original generator.
-/
noncomputable section
namespace Verification.OriginalZeroLayerCast
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) {I J : Finset (Fin n)}

def equiv (h : I=J) : GlobalNormalFrame.ZeroLayer R κ n I B ≃ₐ[R] GlobalNormalFrame.ZeroLayer R κ n J B := by
  subst J
  exact AlgEquiv.refl

theorem original (h : I=J) (a : Fin n ⊕ κ) : equiv R κ n B h
    (ExplicitStratumCoordinates.original R κ n I B a)=ExplicitStratumCoordinates.original R κ n J B a := by
  subst J
  rfl

#print axioms equiv
#print axioms original
end Verification.OriginalZeroLayerCast
