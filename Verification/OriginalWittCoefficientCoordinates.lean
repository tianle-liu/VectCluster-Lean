/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittCoordinateQuotient
import Verification.GroupAlgebraScalarExtension

/-!
# Original Witt Coefficient Coordinates

Extension of the original integral quotient by arbitrary coefficients,
with the actual coordinate splitting and signed monomial formula retained.
-/
noncomputable section
open scoped Classical TensorProduct
namespace Verification.OriginalWittCoefficientCoordinates
open Verification.OriginalWittQuotient Verification.OriginalWittCharacterSplitting
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (hz : ∀ i j : I, B (Sum.inl j.val) (Sum.inl i.val)=0)
variable (A : Type*) [AddCommGroup A]

def equiv : Stratum (fun a v => B a (Sum.inl v)) I ⊗[ℤ] A ≃ₗ[ℤ]
    (Multiplicative (Fin (ExplicitStratumTorus.torusRank κ n I B) → ZMod 2) →₀ A) :=
  GroupAlgebraScalarExtension.equiv (OriginalWittCoordinateQuotient.equiv κ n I B hf hs hz).toLinearEquiv

theorem monomial (m : Bits (Fin n) κ) (a : A) :
    equiv κ n I B hf hs hz A (Ideal.Quotient.mk _
      (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m)) ⊗ₜ[ℤ] a) =
      Finsupp.single (Multiplicative.ofAdd (splitting κ n I B hf hs m).2)
        ((BinarySignedFiber.character (OriginalWittStratumFree.signs I)
          (Multiplicative.ofAdd (splitting κ n I B hf hs m).1) : ℤ) • a) := by
  apply GroupAlgebraScalarExtension.single
  exact (OriginalWittCoordinateQuotient.monomial κ n I B hf hs hz m).trans
    (GroupAlgebraScalarExtension.scalar_monomial _ _)

#print axioms equiv
#print axioms monomial
end Verification.OriginalWittCoefficientCoordinates
