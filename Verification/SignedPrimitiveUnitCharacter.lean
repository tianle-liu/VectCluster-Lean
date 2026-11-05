/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignedPrimitiveFiberUnits
import Verification.OriginalASMonomialUnits

/-!
# Signed Primitive Unit Character

The explicit translated monomial units form a genuine character of
the original integral lattice.
-/
noncomputable section
open scoped Classical
namespace Verification.SignedPrimitiveUnitCharacter
variable {R ι κ : Type*} [CommRing R] [Fintype κ]
variable (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (hf : Function.Injective f)
variable (hs : FreezingLattice.Saturated (LinearMap.range f)) (u : ι → Rˣ)

def character : Multiplicative (κ →₀ ℤ) →*
    (MonoidAlgebra R (Multiplicative (Fin (Module.finrank ℤ ((κ →₀ ℤ) ⧸ LinearMap.range f)) →₀ ℤ)))ˣ where
  toFun m := SignedPrimitiveFiberUnits.unit f hf hs u (Multiplicative.toAdd m)
  map_one' := by simp [SignedPrimitiveFiberUnits.unit]
  map_mul' a b := by
    simp only [SignedPrimitiveFiberUnits.unit,toAdd_mul,map_add,Prod.fst_add,Prod.snd_add,
      ofAdd_add,map_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem character_apply (m : κ →₀ ℤ) : character f hf hs u (Multiplicative.ofAdd m) =
    SignedPrimitiveFiberUnits.unit f hf hs u m := rfl

#print axioms character
#print axioms character_apply
end Verification.SignedPrimitiveUnitCharacter

namespace Verification.OriginalASUnitCharacter
open Verification.IndependentChartIndex Verification.OriginalASMonomialUnits
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,FrozenAcyclicCover.earlierWeights κ n B i j=0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)

def character : Multiplicative ((Other n I ⊕ κ) →₀ ℤ) →* (GlobalNormalFrame.ZeroLayer R κ n I B)ˣ :=
  (Units.map (inclusion R κ n I B hf hs hpos hneg hsupport hI).toRingHom.toMonoidHom).comp
    (SignedPrimitiveUnitCharacter.character (GlobalExchangeSmooth.selectedMap κ n B I) hf hs (fun _ => (-1:Rˣ)))

theorem character_apply (m : (Other n I ⊕ κ) →₀ ℤ) :
    character R κ n I B hf hs hpos hneg hsupport hI (Multiplicative.ofAdd m) =
      unit R κ n I B hf hs hpos hneg hsupport hI m := rfl

#print axioms character
#print axioms character_apply
end Verification.OriginalASUnitCharacter
