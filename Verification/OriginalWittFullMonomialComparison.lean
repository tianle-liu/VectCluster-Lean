/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittNormalRemoval
import Verification.OriginalWittMonomialComparison

/-!
# Original Witt Full Monomial Comparison

Every literal group-ring basis element, including arbitrary normal
bits, has the actual original-coordinate Witt form as its section image.
-/
noncomputable section
open scoped Classical TensorProduct
namespace Verification.OriginalWittFullMonomialComparison
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput Verification.OriginalWittNormalRemoval
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,FrozenAcyclicCover.earlierWeights κ n B i j=0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)
variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0}) (D : Symbols R W)
variable (T : TorusBasis R W D) (H : WittSheafAffineInvariance.Standard R W)

theorem monomial (m : OriginalWittQuotient.Bits (Fin n) κ) (a : RingSection W R) :
    OriginalWittSectionCoordinates.equiv R κ n I B hf hs hpos hneg hsupport hI W D T H
      (Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m)) ⊗ₜ[ℤ] a) =
    form R W D _ (OriginalASMonomialUnits.smooth R κ n I B hf hs hpos hneg hsupport hI)
      (OriginalASMonomialUnits.unit R κ n I B hf hs hpos hneg hsupport hI
        (integerOutside κ n I m)) *
        pullback W (algebraMap R (GlobalNormalFrame.ZeroLayer R κ n I B)) a := by
  have h := quotient_remove κ n I B m
  change Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m)) =
    Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd (remove κ n I m))) at h
  rw [h,← exponent_integerOutside]
  exact OriginalWittMonomialComparison.original_monomial_coefficient R κ n I B hf hs hpos hneg hsupport hI W D T H _ a

#print axioms monomial
end Verification.OriginalWittFullMonomialComparison
