/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalBoundaryUnitExtensions
import Verification.RostReducedExtendedUnits
import Verification.ActualFlagSmoothTame

/-!
# Original Boundary Residue Generators

Residues of the actual coefficient units and coordinate selectors.
All extensions and branch multiplicities are constructed from the exchange
presentation; the only residue input is the uniform ordinary DVR rule.
-/
noncomputable section
namespace Verification.OriginalBoundaryResidueGenerators
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
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
local notation "S" => RemainingRing R κ n (J.erase v.val) B
local notation "Q" => GlobalNormalFrame.ZeroLayer R κ n (J.erase v.val) B
local notation "se" => OriginalBoundaryUnitExtensions.sourceEquiv R κ n J B v
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable {m : ℕ} (sm : Basis.SmithNormalForm
  (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)) (Other n J ⊕ κ) m)
variable (he : ∀ i, IsUnit ((sm.a i).natAbs : R))
local notation "inc" => OriginalRemainingCoordinates.inclusion R κ n I B hpos hneg hsupport
  (OriginalRemainingExtension.old_independent κ n J B v hJ)
local notation "f" => OriginalRemainingExtension.extension R κ n J B v hpos hneg hsupport hJ hf

include hpos hneg hsupport hJ hf in
theorem regular : IsRegular (OriginalBoundaryBranches.parameter R κ n J B v) := by
  have h : IsLeftRegular (OriginalBoundaryBranches.parameter R κ n J B v) :=
    OriginalBoundaryBranches.parameter_regular R κ n J B v hpos hneg hsupport hJ hf
  exact ⟨h, h.right_of_commute (fun b => mul_comm _ b)⟩

variable {K : Type} (D : K → Type) [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
variable (de : GlobalNormalFrame.ZeroLayer R κ n J B ≃+* ∀ j, D j) (j : K)
local notation "ce" => RingEquiv.trans (OriginalBoundaryBranches.closedEquiv R κ n J B v) de
local notation "ht" => regular R κ n J B v hpos hneg hsupport hJ hf
local notation "hB" => matrix_zero_block κ n J B hpos hneg hsupport hJ

def residue : Additive Qˣ →+ ℤ := by
  letI : Algebra.Smooth R W := ActualFlagSmoothTame.old_smooth R κ n J B v hB hf sm he
  letI : Algebra.Smooth W (RostPrincipalLocalizationInput.OpenRing W t) :=
    Algebra.Smooth.of_isLocalization_Away t
  letI : Algebra.Smooth R (RostPrincipalLocalizationInput.OpenRing W t) := Algebra.Smooth.comp R W _
  exact (RostReducedDivisorResidues.residue T P F Z E U R W t ht D ce j).comp
    (Units.map (se).toMonoidHom).toAdditive

include N in
theorem coefficient (u : Sˣ) :
    residue T P F Z E U R κ n J B v hpos hneg hsupport hJ hf sm he D de j
      (Additive.ofMul (Units.map (inc).toMonoidHom u)) = 0 := by
  letI : Algebra.Smooth R W := ActualFlagSmoothTame.old_smooth R κ n J B v hB hf sm he
  letI : Algebra.Smooth W (RostPrincipalLocalizationInput.OpenRing W t) :=
    Algebra.Smooth.of_isLocalization_Away t
  letI : Algebra.Smooth R (RostPrincipalLocalizationInput.OpenRing W t) := Algebra.Smooth.comp R W _
  letI : IsNoetherianRing W := OriginalBoundaryBranches.ambient_noetherian R κ n J B v hpos hneg hsupport hJ hf sm he
  change RostReducedDivisorResidues.residue T P F Z E U R W t ht D ce j
    (Additive.ofMul (Units.map (se).toMonoidHom (Units.map (inc).toMonoidHom u))) = 0
  rw [OriginalBoundaryUnitExtensions.open_coefficient_unit R κ n J B v hpos hneg hsupport hJ hf]
  exact RostReducedExtendedUnits.extended_map T P F Z E U N R W t ht D ce j _

include N in
theorem complement_selector (a : S) (ha : a * a = a) (k : Other n J ⊕ κ)
    (u : Qˣ) (hu : (u : Q) = ExplicitStratumCoordinates.original R κ n I B
      (IndependentChartPresentation.complementEmbedding κ n J k)) :
    residue T P F Z E U R κ n J B v hpos hneg hsupport hJ hf sm he D de j
      (Additive.ofMul (BoundaryComponentSelector.unit (inc a) ((map_mul (inc) a a).symm.trans (congrArg (inc) ha)) u)) = 0 := by
  letI : Algebra.Smooth R W := ActualFlagSmoothTame.old_smooth R κ n J B v hB hf sm he
  letI : Algebra.Smooth W (RostPrincipalLocalizationInput.OpenRing W t) :=
    Algebra.Smooth.of_isLocalization_Away t
  letI : Algebra.Smooth R (RostPrincipalLocalizationInput.OpenRing W t) := Algebra.Smooth.comp R W _
  letI : IsNoetherianRing W := OriginalBoundaryBranches.ambient_noetherian R κ n J B v hpos hneg hsupport hJ hf sm he
  obtain ⟨w, hw⟩ := OriginalBoundaryUnitExtensions.complement_selector_extends
    R κ n J B v hpos hneg hsupport hJ hf a ha k u hu
  change RostReducedDivisorResidues.residue T P F Z E U R W t ht D ce j
    (Additive.ofMul (Units.map (se).toMonoidHom
      (BoundaryComponentSelector.unit (inc a) ((map_mul (inc) a a).symm.trans (congrArg (inc) ha)) u))) = 0
  rw [hw]
  exact RostReducedExtendedUnits.extended_map T P F Z E U N R W t ht D ce j w

variable {L : Type} [Finite L] (C : L → Type) [∀ l, CommRing (C l)]
variable (c : RemainingRing R κ n (J.erase v.val) B ≃+* ∀ l, C l)

include N in
theorem parameter_selector (l : L) (u : Qˣ)
    (hu : (u : Q) = ExplicitStratumCoordinates.original R κ n I B (Sum.inl v.val)) :
    residue T P F Z E U R κ n J B v hpos hneg hsupport hJ hf sm he D de j
      (Additive.ofMul (BoundaryComponentSelector.unit
        (inc (ProductComponentIdempotents.indicator C c l))
        ((map_mul (inc) _ _).symm.trans (congrArg (inc)
          (ProductComponentIdempotents.indicator_idempotent C c l))) u)) =
      @ite ℤ (BranchComponentPullback.sourcePoint t D ce j f ∈
        Set.range (StratumComponents.componentMap C c l)) (Classical.propDecidable _) 1 0 := by
  letI : Algebra.Smooth R W := ActualFlagSmoothTame.old_smooth R κ n J B v hB hf sm he
  letI : Algebra.Smooth W (RostPrincipalLocalizationInput.OpenRing W t) :=
    Algebra.Smooth.of_isLocalization_Away t
  letI : Algebra.Smooth R (RostPrincipalLocalizationInput.OpenRing W t) := Algebra.Smooth.comp R W _
  letI : IsNoetherianRing W := OriginalBoundaryBranches.ambient_noetherian R κ n J B v hpos hneg hsupport hJ hf sm he
  apply RostReducedDivisorResidues.selector_component_pullback T P F Z E U N R W t ht D ce j C c f l
  exact OriginalBoundaryUnitExtensions.open_parameter_selector R κ n J B v hpos hneg hsupport hJ hf
    _ (ProductComponentIdempotents.indicator_idempotent C c l) u hu

#print axioms regular
#print axioms residue
#print axioms coefficient
#print axioms complement_selector
#print axioms parameter_selector
end Verification.OriginalBoundaryResidueGenerators
