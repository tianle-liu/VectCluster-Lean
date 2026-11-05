/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalChowIncoming
import Verification.OriginalRostBoundaryValues

/-!
# Original Chow Boundary Expansion

Finite block expansion of the actual original Chow incoming map.
This proves its relation to the principal-residue blocks without replacing
the original map by a separately postulated matrix.
-/
noncomputable section
namespace Verification.OriginalChowBoundaryExpansion
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Classical
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I,Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I⊕κ) m),∀ i,IsUnit ((sm.a i).natAbs : R))


variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (Z : RostWeightZero.IntegralConvention T) (p : ℕ)
local notation "A" => Global R κ n B
local notation "xs" => (initial R κ n B ∘ Sum.inl)
local notation "Allowed" => Independent (laterWeights κ n B)
local notation "D" => OriginalRostSupport.support T S R κ n B hpos hneg hsupport hf htame ((p+1:ℕ):ℤ)

def sourceUnits (I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) p) :
    RostCanonicalCoefficients.Sections T (GlobalNormalFrame.ZeroLayer R κ n I.val B) 1 ≅
      AddCommGrp.of (Additive (GlobalNormalFrame.ZeroLayer R κ n I.val B)ˣ) := by
  letI := OriginalRostBoundaryValues.source_smooth R κ n B hpos hneg hsupport hf htame I.val I.property.2
  exact U.units R (GlobalNormalFrame.ZeroLayer R κ n I.val B)

def input (a : OriginalChowIncoming.UnitsTerm R κ n B (p+1)) :
    RostSupportInput.Layer T A (Fin n) xs Allowed ((p+1:ℕ):ℤ) p 0 :=
  fun I => (RostChowBlock.sourceIso T A (Fin n) xs Allowed p I).inv
    ((sourceUnits T R κ n B hpos hneg hsupport hf htame U p I).inv (a I))

theorem apply (a : OriginalChowIncoming.UnitsTerm R κ n B (p+1))
    (J : PrimeLayerCover.Index (Independent (laterWeights κ n B)) (p+1))
    (c : ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n J.val B))) :
    OriginalChowIncoming.lastDifferential T F S R κ n B hpos hneg hsupport hf htame U Z (p+1)
      (Nat.zero_lt_succ p) a J c =
    ∑ I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) p,
      (OriginalRostComponentTerms.stratumComponents T F R κ n B hpos hneg hsupport hf htame Z J.val J.property.2).hom
        (OriginalRostBoundaryValues.block R κ n B hpos hneg hsupport hf htame T S p I J
          ((sourceUnits T R κ n B hpos hneg hsupport hf htame U p I).inv (a I))) c := by
  change (OriginalRostComponentTerms.stratumComponents T F R κ n B hpos hneg hsupport hf htame Z J.val J.property.2).hom
    ((RostChowBlock.targetIso T A (Fin n) xs Allowed p J).hom
      (RostSupportRowBlocks.differential T A (Fin n) xs Allowed ((p+1:ℕ):ℤ) (D) p
        (input T R κ n B hpos hneg hsupport hf htame U p a) J)) c = _
  rw [RostSupportRowBlocks.differential_apply]
  simp only [map_sum,Finset.sum_apply]
  rfl

theorem single (I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) p)
    (u : Additive (GlobalNormalFrame.ZeroLayer R κ n I.val B)ˣ)
    (J : PrimeLayerCover.Index (Independent (laterWeights κ n B)) (p+1))
    (c : ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n J.val B))) :
    OriginalChowIncoming.lastDifferential T F S R κ n B hpos hneg hsupport hf htame U Z (p+1)
      (Nat.zero_lt_succ p) (Pi.single I u) J c =
    (OriginalRostComponentTerms.stratumComponents T F R κ n B hpos hneg hsupport hf htame Z J.val J.property.2).hom
      (OriginalRostBoundaryValues.block R κ n B hpos hneg hsupport hf htame T S p I J
        ((sourceUnits T R κ n B hpos hneg hsupport hf htame U p I).inv u)) c := by
  rw [apply]
  rw [Finset.sum_eq_single I]
  · simp only [Pi.single_eq_same]
  · intro L _ hL
    simp only [Pi.single_eq_of_ne hL,map_zero,Pi.zero_apply]
  · simp

#print axioms sourceUnits
#print axioms input
#print axioms apply
#print axioms single
end Verification.OriginalChowBoundaryExpansion
