/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittCharacterSplitting
import Verification.BinarySignedCharacterSum
import Verification.OriginalWittStratumFree

/-!
# Original Witt Outside Bits

The original nonvanishing character lattice inside the full binary
exponent lattice, with its exact signed image in the fixed AS splitting.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalWittOutsideBits
open Verification.IndependentChartIndex Verification.OriginalWittCharacterSplitting
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

def exponent (m : (Other n I ⊕ κ) →₀ ℤ) : OriginalWittQuotient.Bits (Fin n) κ :=
  (splitBits κ n I).symm (0,fun i => (m i : ZMod 2))

theorem splitting_exponent (m : (Other n I ⊕ κ) →₀ ℤ) :
    splitting κ n I B hf hs (exponent κ n I m) =
      (Sum.elim (fun _ => 0) (fun i => ((ExplicitStratumTorus.splitting κ n I B hf hs m).1 i : ZMod 2)),
        fun j => ((ExplicitStratumTorus.splitting κ n I B hf hs m).2 j : ZMod 2)) := by
  dsimp only [splitting,exponent,LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.prodCongr_apply,LinearEquiv.refl_apply]
  rw [IntegerReductionEquiv.productEquiv_cast]
  rfl

theorem sign_exponent (m : (Other n I ⊕ κ) →₀ ℤ) :
    BinarySignedFiber.character (OriginalWittStratumFree.signs I)
      (Multiplicative.ofAdd (splitting κ n I B hf hs (exponent κ n I m)).1) =
      PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (fun _ : I => (-1:ℤˣ))
        (Multiplicative.ofAdd (ExplicitStratumTorus.splitting κ n I B hf hs m).1) := by
  rw [splitting_exponent]
  exact BinarySignedCharacterSum.character_right_cast _

#print axioms exponent
#print axioms splitting_exponent
#print axioms sign_exponent
end Verification.OriginalWittOutsideBits
