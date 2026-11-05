/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStratumUnitGeneration
import Verification.OriginalFreeBoundaryIndex
import Verification.OriginalBoundaryResidueGenerators

/-!
# Original Adjacent Unit Residue Formula

Every adjacent residue of an actual original-stratum unit is the
integer exponent of the new boundary coordinate, summed over the source
components whose pullbacks contain the target branch.
-/
noncomputable section
namespace Verification.OriginalAdjacentUnitResidueFormula
attribute [local instance] Classical.propDecidable
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open scoped BigOperators
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
open Verification.OriginalFreeTorusCoordinates
variable (T : RostAffineInput.Theory) (P : RostPrincipalLocalizationInput.Theory T)
variable (F : RostFiniteProducts.Standard T) (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (N : RostPrincipalResidueInput.Normalization T P F Z E U)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : J)
local notation "I" => J.erase v.val
local notation "W" => OriginalBoundaryBranches.Ambient R κ n J B v
local notation "t" => OriginalBoundaryBranches.parameter R κ n J B v
local notation "Q" => GlobalNormalFrame.ZeroLayer R κ n I B
local notation "S" => RemainingRing R κ n I B
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable {m : ℕ} (sm : Basis.SmithNormalForm
  (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)) (Other n J ⊕ κ) m)
variable (he : ∀ i, IsUnit ((sm.a i).natAbs : R))
variable {K : Type} (D : K → Type) [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
variable (de : GlobalNormalFrame.ZeroLayer R κ n J B ≃+* ∀ j, D j) (j : K)
variable (Src : OriginalRetainedProductCoordinates.ProductData R κ n (J.erase v.val) B)
local notation "hI" => OriginalRemainingExtension.old_independent κ n J B v hJ
local notation "inc" => OriginalRemainingCoordinates.inclusion R κ n I B hpos hneg hsupport hI
local notation "f" => OriginalRemainingExtension.extension R κ n J B v hpos hneg hsupport hJ hf
local notation "ce" => RingEquiv.trans (OriginalBoundaryBranches.closedEquiv R κ n J B v) de
local notation "b" => OriginalFreeBoundaryIndex.boundary κ n J B v hpos hneg hsupport hJ
local notation "ρ" => OriginalBoundaryResidueGenerators.residue T P F Z E U R κ n J B v
  hpos hneg hsupport hJ hf sm he D de j
local notation "ou" => OriginalStratumUnitGeneration.originalUnit R κ n I B Src hpos hneg hsupport hI
local notation "sel" => OriginalStratumUnitGeneration.selector R κ n I B Src hpos hneg hsupport hI

def componentWeight (l : Src.Index) : ℤ :=
  if BranchComponentPullback.sourcePoint t D ce j f ∈
    Set.range (StratumComponents.componentMap Src.Factor Src.equiv.toRingEquiv l) then 1 else 0

include N in
theorem complement_selector (l : Src.Index) (k : FreeIndex κ n I B) (hne : k ≠ b) :
    ρ (Additive.ofMul (sel l k)) = 0 := by
  apply OriginalBoundaryResidueGenerators.complement_selector T P F Z E U N R κ n J B v
    hpos hneg hsupport hJ hf sm he D de j
    (ProductComponentIdempotents.indicator Src.Factor Src.equiv.toRingEquiv l)
    (ProductComponentIdempotents.indicator_idempotent Src.Factor Src.equiv.toRingEquiv l)
    (OriginalFreeBoundaryIndex.complement κ n J B v hpos hneg hsupport hJ k hne)
    (ou k)
  rw [OriginalStratumUnitGeneration.originalUnit_val,
    OriginalFreeBoundaryIndex.complement_original]

include N in
theorem boundary_selector (l : Src.Index) :
    ρ (Additive.ofMul (sel l b)) =
      componentWeight R κ n J B v hpos hneg hsupport hJ hf D de j Src l := by
  apply OriginalBoundaryResidueGenerators.parameter_selector T P F Z E U N R κ n J B v
    hpos hneg hsupport hJ hf sm he D de j Src.Factor Src.equiv.toRingEquiv l (ou b)
  rw [OriginalStratumUnitGeneration.originalUnit_val,
    OriginalFreeBoundaryIndex.boundary_original]

include N in
theorem selector (l : Src.Index) (k : FreeIndex κ n I B) :
    ρ (Additive.ofMul (sel l k)) =
      if k = b then componentWeight R κ n J B v hpos hneg hsupport hJ hf D de j Src l else 0 := by
  by_cases hk : k = b
  · subst k
    rw [if_pos rfl]
    exact boundary_selector T P F Z E U N R κ n J B v hpos hneg hsupport hJ hf sm he D de j Src l
  · rw [if_neg hk]
    exact complement_selector T P F Z E U N R κ n J B v hpos hneg hsupport hJ hf sm he D de j Src l k hk

include N in
theorem residue (u : Qˣ) :
    ρ (Additive.ofMul u) =
      ∑ l, (OriginalStratumUnitGeneration.exponentPart R κ n I B Src hpos hneg hsupport hI u l b) *
        componentWeight R κ n J B v hpos hneg hsupport hJ hf D de j Src l := by
  rw [OriginalStratumUnitGeneration.additive_decomposition R κ n I B Src hpos hneg hsupport hI ρ u]
  have hc : ρ (Additive.ofMul (OriginalStratumUnitGeneration.coefficientUnit R κ n I B
    hpos hneg hsupport hI (OriginalStratumUnitGeneration.constantPart R κ n I B Src hpos hneg hsupport hI u))) = 0 :=
    OriginalBoundaryResidueGenerators.coefficient T P F Z E U N R κ n J B v
      hpos hneg hsupport hJ hf sm he D de j _
  rw [hc, zero_add]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [selector T P F Z E U N R κ n J B v hpos hneg hsupport hJ hf sm he D de j Src,
    zsmul_eq_mul]
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl]
    simp only [Int.cast_id]
  · intro k hk hkb
    rw [if_neg hkb, mul_zero]
  · intro hb
    exact False.elim (hb (Finset.mem_univ b))

#print axioms componentWeight
#print axioms complement_selector
#print axioms boundary_selector
#print axioms selector
#print axioms residue
end Verification.OriginalAdjacentUnitResidueFormula
