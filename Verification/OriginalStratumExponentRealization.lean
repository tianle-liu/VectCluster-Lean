/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStratumUnitGeneration

/-!
# Original Stratum Exponent Realization

Every collection of integral exponents is realized by an actual
unit of the original stratum, independently for every retained component
and original free coordinate. This is an explicit inverse, not a new
surjectivity premise.
-/
noncomputable section
namespace Verification.OriginalStratumExponentRealization
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (D : OriginalRetainedProductCoordinates.ProductData R κ n I B)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, FrozenAcyclicCover.earlierWeights κ n B i j = 0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j = 0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)
local notation "A" => GlobalNormalFrame.ZeroLayer R κ n I B
local notation "K" => FreeIndex κ n I B
local notation "V" => Selected n I

def realize (a : D.Index → K →₀ ℤ) : Aˣ :=
  (OriginalStratumUnitGeneration.transport R κ n I B D hpos hneg hsupport hI).symm
    ((AffineComponentUnits.coordinates D.Factor V K).symm
      (fun j => (1, Multiplicative.ofAdd (a j))))

theorem exponent_realize (a : D.Index → K →₀ ℤ) (j : D.Index) :
    OriginalStratumUnitGeneration.exponentPart R κ n I B D hpos hneg hsupport hI
      (realize R κ n I B D hpos hneg hsupport hI a) j = a j := by
  unfold OriginalStratumUnitGeneration.exponentPart AffineComponentUnitGeneration.exponentPart realize
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

theorem exponents_surjective : Function.Surjective
    (OriginalStratumUnitGeneration.exponentPart R κ n I B D hpos hneg hsupport hI) := by
  intro a
  exact ⟨realize R κ n I B D hpos hneg hsupport hI a,
    funext (exponent_realize R κ n I B D hpos hneg hsupport hI a)⟩

def integerExponents (u : Aˣ) (j : D.Index) (k : K) : ℤ :=
  OriginalStratumUnitGeneration.exponentPart R κ n I B D hpos hneg hsupport hI u j k

theorem integerExponents_surjective : Function.Surjective
    (integerExponents R κ n I B D hpos hneg hsupport hI) := by
  intro a
  refine ⟨realize R κ n I B D hpos hneg hsupport hI
    (fun j => Finsupp.equivFunOnFinite.symm (a j)), ?_⟩
  funext j k
  change OriginalStratumUnitGeneration.exponentPart R κ n I B D hpos hneg hsupport hI _ j k = a j k
  rw [exponent_realize]
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply (a j)) k

#print axioms realize
#print axioms exponent_realize
#print axioms exponents_surjective
#print axioms integerExponents
#print axioms integerExponents_surjective
end Verification.OriginalStratumExponentRealization
