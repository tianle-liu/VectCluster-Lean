/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalAdjacentComponentFormula
import Verification.OriginalChowExponentFamily
import Verification.AllowedPredecessorSum

/-!
# Original Chow Whole Boundary

The actual original Chow incoming differential is the sum of exponent
pullbacks along the constructed maps of actual connected components.
All source units are allowed. The formula is derived from ordinary Rost
residues; no component-matrix compatibility is postulated.
-/
noncomputable section
namespace Verification.OriginalChowWholeBoundary
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I ⊕ κ) m), ∀ i, IsUnit ((sm.a i).natAbs : R))
variable (p : ℕ)
local notation "Allowed" => ExchangeOpenCover.Independent (laterWeights κ n B)
local notation "Source" => AllowedComponentRow.Source Allowed p
local notation "Target" => AllowedComponentRow.Target Allowed p
local notation "pred" => AllowedComponentRow.predecessor Allowed (OriginalChowExponentFamily.hereditary κ n B) p
variable (D : ∀ I : AllowedComponentRow.Source (ExchangeOpenCover.Independent (laterWeights κ n B)) p,
  OriginalRetainedProductCoordinates.ProductData R κ n I.val B)

def componentMap (J : Target) (v : J.val) :
    OriginalChowExponentFamily.Components R κ n B J.val →
      OriginalChowExponentFamily.Components R κ n B (pred J v).val :=
  OriginalBoundaryComponentMap.componentMap R κ n J.val B v hpos hneg hsupport J.property.2
    (hf J.val J.property.2) (D (pred J v))

variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T) (P : RostPrincipalLocalizationInput.Theory T)
variable (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (UN : RostCanonicalCoefficients.UnitsNaturality T F U)
variable (N : RostPrincipalResidueInput.Normalization T P F Z E U)
variable (C : OriginalRostBoundaryCharts.Standard R κ n B hpos hneg hsupport hf htame T S P)
local notation "δ" => OriginalChowIncoming.lastDifferential T F S R κ n B hpos hneg hsupport hf htame U Z (p+1) (Nat.zero_lt_succ p)
local notation "r" => componentMap R κ n B hpos hneg hsupport hf p D

include C in
theorem single_nonincident (I : Source) (J : Target) (h : ¬ I.val ⊆ J.val)
    (u : Additive (GlobalNormalFrame.ZeroLayer R κ n I.val B)ˣ)
    (c : OriginalChowExponentFamily.Components R κ n B J.val) :
    δ (Pi.single I u) J c = 0 := by
  rw [OriginalChowBoundaryExpansion.single]
  rw [OriginalRostBoundaryValues.nonincident R κ n B hpos hneg hsupport hf htame T S P C p I J h]
  change (OriginalRostComponentTerms.stratumComponents T F R κ n B hpos hneg hsupport hf htame Z J.val J.property.2).hom 0 c = 0
  simp only [map_zero, Pi.zero_apply]

include C UN N in
theorem single (J : Target) (v : J.val)
    (u : Additive (GlobalNormalFrame.ZeroLayer R κ n (pred J v).val B)ˣ)
    (c : OriginalChowExponentFamily.Components R κ n B J.val) :
    δ (Pi.single (pred J v) u) J c =
      OriginalComponentExponentCoordinates.exponents R κ n (pred J v).val B (D (pred J v))
        hpos hneg hsupport (pred J v).property.2 (Additive.toMul u) v.val (r J v c) := by
  let d := OriginalRostComponentTerms.decomposition R κ n B hpos hneg hsupport hf htame J.val J.property.2
  let j := DomainProductComponents.transport d.Factor d.equiv c
  have hc : c = ConnectedComponents.mk (RostComponentEvaluation.point d.Factor d.equiv j) := by
    apply (DomainProductComponents.transport d.Factor d.equiv).injective
    exact (RostComponentEvaluation.point_component d.Factor d.equiv j).symm
  rw [hc]
  exact OriginalAdjacentComponentFormula.single R κ n B hpos hneg hsupport hf htame p J v
    T F S P Z E U UN N C (D (pred J v)) j (Additive.toMul u)

include C UN N in
theorem apply (u : OriginalChowIncoming.UnitsTerm R κ n B (p+1))
    (J : Target) (c : OriginalChowExponentFamily.Components R κ n B J.val) :
    δ u J c = ∑ v : J.val,
      OriginalChowExponentFamily.flags R κ n B p D hpos hneg hsupport u J v (r J v c) := by
  calc
    δ u J c = ∑ I : Source, δ (Pi.single I (u I)) J c := by
      rw [OriginalChowBoundaryExpansion.apply]
      apply Finset.sum_congr rfl
      intro I _
      exact (OriginalChowBoundaryExpansion.single T F S R κ n B hpos hneg hsupport hf htame U Z p I (u I) J c).symm
    _ = ∑ v : J.val, δ (Pi.single (pred J v) (u (pred J v))) J c := by
      have hs := AllowedPredecessorSum.sum Allowed (OriginalChowExponentFamily.hereditary κ n B) p J
        (fun I : Source => δ (Pi.single I (u I)) J c)
        (fun I h => single_nonincident R κ n B hpos hneg hsupport hf htame p T F S P Z U C I J h (u I) c)
      dsimp only at hs
      have hfin : Fintype.ofFinite Source = (inferInstance : Fintype Source) := Subsingleton.elim _ _
      rw [hfin] at hs
      exact hs
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      exact single R κ n B hpos hneg hsupport hf htame p D T F S P Z E U UN N C J v (u (pred J v)) c

include C UN N in
theorem blockMap_eq (u : OriginalChowIncoming.UnitsTerm R κ n B (p+1)) :
    δ u = AllowedComponentRow.blockMap Allowed (OriginalChowExponentFamily.hereditary κ n B) p
      (OriginalChowExponentFamily.componentFamily R κ n B p)
      (fun J : Target => OriginalChowExponentFamily.Components R κ n B J.val) r
      (OriginalChowExponentFamily.flags R κ n B p D hpos hneg hsupport u) := by
  funext J c
  exact apply R κ n B hpos hneg hsupport hf htame p D T F S P Z E U UN N C u J c

#print axioms componentMap
#print axioms single_nonincident
#print axioms single
#print axioms apply
#print axioms blockMap_eq
end Verification.OriginalChowWholeBoundary
