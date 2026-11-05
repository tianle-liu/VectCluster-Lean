/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRetainedProductCoordinates
import Verification.OriginalRemainingExtension
import Verification.IdempotentComponentEquivalence
import Verification.RostComponentEvaluation
import Verification.BranchComponentPullback

/-!
# Original Boundary Component Map

The component map in the Chow formula. The genuine closed-boundary
map is Spec(O_J) → Spec(Y_I). The proved component bijection induced by
Y_I → O_I identifies its target with components of the old stratum.
No scheme map from the closed stratum to the punctured old stratum is used.
-/
noncomputable section
namespace Verification.OriginalBoundaryComponentMap
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
open Verification.FrozenAcyclicCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : J)
local notation "I" => J.erase v.val
local notation "W" => OriginalBoundaryBranches.Ambient R κ n J B v
local notation "t" => OriginalBoundaryBranches.parameter R κ n J B v
local notation "Y" => RemainingRing R κ n (J.erase v.val) B
local notation "A" => Global R κ n B
local notation "xs" => (initial R κ n B ∘ Sum.inl)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable (D : OriginalRetainedProductCoordinates.ProductData R κ n (J.erase v.val) B)

abbrev SourceFactor (i : D.Index) :=
  MvPolynomial (Selected n I) (OriginalTorus.Torus (D.Factor i) (FreeIndex κ n I B))

def sourceEquiv : GlobalNormalFrame.ZeroLayer R κ n I B ≃+* ∀ i,SourceFactor R κ n J B v D i :=
  (OriginalRetainedProductCoordinates.stratumEquiv R κ n I B D hpos hneg hsupport
    (OriginalRemainingExtension.old_independent κ n J B v hJ)).toRingEquiv

def coefficientComponents : ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B)) ≃
    ConnectedComponents (PrimeSpectrum Y) :=
  IdempotentComponentEquivalence.components D.Factor (SourceFactor R κ n J B v D)
    D.equiv.toRingEquiv (sourceEquiv R κ n J B v hpos hneg hsupport hJ D)

theorem coefficientComponents_mk (p : PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B)) :
    coefficientComponents R κ n J B v hpos hneg hsupport hJ D (ConnectedComponents.mk p) =
    ConnectedComponents.mk (PrimeSpectrum.comap
      (OriginalRemainingCoordinates.inclusion R κ n I B hpos hneg hsupport
        (OriginalRemainingExtension.old_independent κ n J B v hJ)).toRingHom p) :=
  IdempotentComponentEquivalence.components_mk D.Factor (SourceFactor R κ n J B v D)
    D.equiv.toRingEquiv (sourceEquiv R κ n J B v hpos hneg hsupport hJ D) _
    (OriginalRetainedProductCoordinates.inclusion_indicator R κ n I B D hpos hneg hsupport
      (OriginalRemainingExtension.old_independent κ n J B v hJ)) p

theorem closedEquiv_eq_target :
    OriginalBoundaryBranches.closedEquiv R κ n J B v =
      (AdjacentStratumLocalization.targetEquiv A (Fin n) xs J v).toRingEquiv := rfl

/-- The actual ring map O(Y_I) → O(O_J), obtained by reduction modulo
 the boundary parameter and the constructed closed-chart identification. -/
def closedExtension : Y →+* GlobalNormalFrame.ZeroLayer R κ n J B :=
  (AdjacentStratumLocalization.targetEquiv A (Fin n) xs J v).toRingEquiv.toRingHom.comp
    ((Ideal.Quotient.mk (Ideal.span {t})).comp
      (OriginalRemainingExtension.extension R κ n J B v hpos hneg hsupport hJ hf))

theorem closedExtension_generator (a : RemainingIndex κ n I B) :
    closedExtension R κ n J B v hpos hneg hsupport hJ hf
      (Ideal.Quotient.mk (remainingIdeal R κ n I B)
        (OriginalTorus.torusCoordinate R (RemainingIndex κ n I B) a)) =
    ExplicitStratumCoordinates.original R κ n J B
      (IndependentChartPresentation.complementEmbedding κ n I a.val) := by
  change AdjacentStratumLocalization.targetEquiv A (Fin n) xs J v
    (Ideal.Quotient.mk _ (OriginalRemainingExtension.extension R κ n J B v hpos hneg hsupport hJ hf _)) = _
  rw [OriginalRemainingExtension.extension,RegularPrincipalExtension.lift_mk]
  have htor : (OriginalRemainingExtension.torusMap R κ n J B v hpos hneg hsupport hJ).toRingHom
      (OriginalTorus.torusCoordinate R (RemainingIndex κ n I B) a) =
    OriginalBoundaryBranches.coordinate R κ n J B v
      (IndependentChartPresentation.complementEmbedding κ n I a.val) :=
    OriginalRemainingExtension.torusMap_coordinate R κ n J B v hpos hneg hsupport hJ a
  rw [htor]
  exact AdjacentStratumLocalization.target_original A (Fin n) xs J v
    (initial R κ n B (IndependentChartPresentation.complementEmbedding κ n I a.val))

/-- The actual map on components in the manuscript, through Y_I. -/
def componentMap : ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n J B)) →
    ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B)) :=
  fun c => (coefficientComponents R κ n J B v hpos hneg hsupport hJ D).symm
    ((PrimeSpectrum.comap (closedExtension R κ n J B v hpos hneg hsupport hJ hf)).continuous.connectedComponentsMap c)

theorem componentMap_mk (p : PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n J B)) :
    coefficientComponents R κ n J B v hpos hneg hsupport hJ D
      (componentMap R κ n J B v hpos hneg hsupport hJ hf D (ConnectedComponents.mk p)) =
    ConnectedComponents.mk (PrimeSpectrum.comap
      (closedExtension R κ n J B v hpos hneg hsupport hJ hf) p) :=
  (coefficientComponents R κ n J B v hpos hneg hsupport hJ D).apply_symm_apply _

def sourceComponent (i : D.Index) : ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B)) :=
  (DomainProductComponents.transport (SourceFactor R κ n J B v D)
    (sourceEquiv R κ n J B v hpos hneg hsupport hJ D)).symm i

theorem componentMap_iff (p : PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n J B)) (i : D.Index) :
    componentMap R κ n J B v hpos hneg hsupport hJ hf D (ConnectedComponents.mk p) =
      sourceComponent R κ n J B v hpos hneg hsupport hJ D i ↔
    PrimeSpectrum.comap (closedExtension R κ n J B v hpos hneg hsupport hJ hf) p ∈
      Set.range (StratumComponents.componentMap D.Factor D.equiv.toRingEquiv i) := by
  change (DomainProductComponents.transport (SourceFactor R κ n J B v D)
    (sourceEquiv R κ n J B v hpos hneg hsupport hJ D)).symm
      (DomainProductComponents.transport D.Factor D.equiv.toRingEquiv
        (ConnectedComponents.mk (PrimeSpectrum.comap
          (closedExtension R κ n J B v hpos hneg hsupport hJ hf) p))) =
    (DomainProductComponents.transport (SourceFactor R κ n J B v D)
      (sourceEquiv R κ n J B v hpos hneg hsupport hJ D)).symm i ↔ _
  rw [((DomainProductComponents.transport (SourceFactor R κ n J B v D)
    (sourceEquiv R κ n J B v hpos hneg hsupport hJ D)).symm.injective.eq_iff)]
  exact DomainProductComponentLabels.label_iff D.Factor D.equiv.toRingEquiv _ i

variable {K : Type} (L : K → Type) [∀ j,CommRing (L j)] [∀ j,IsDomain (L j)]
variable (eJ : GlobalNormalFrame.ZeroLayer R κ n J B ≃+* ∀ j,L j) (j : K)

theorem branch_sourcePoint :
    BranchComponentPullback.sourcePoint t L
      ((AdjacentStratumLocalization.targetEquiv A (Fin n) xs J v).toRingEquiv.trans eJ) j
      (OriginalRemainingExtension.extension R κ n J B v hpos hneg hsupport hJ hf) =
    PrimeSpectrum.comap (closedExtension R κ n J B v hpos hneg hsupport hJ hf)
      (RostComponentEvaluation.point L eJ j) := rfl

theorem branch_component_iff (i : D.Index) :
    BranchComponentPullback.sourcePoint t L
      ((AdjacentStratumLocalization.targetEquiv A (Fin n) xs J v).toRingEquiv.trans eJ) j
      (OriginalRemainingExtension.extension R κ n J B v hpos hneg hsupport hJ hf) ∈
        Set.range (StratumComponents.componentMap D.Factor D.equiv.toRingEquiv i) ↔
    componentMap R κ n J B v hpos hneg hsupport hJ hf D
      (ConnectedComponents.mk (RostComponentEvaluation.point L eJ j)) =
      sourceComponent R κ n J B v hpos hneg hsupport hJ D i := by
  rw [branch_sourcePoint]
  exact (componentMap_iff R κ n J B v hpos hneg hsupport hJ hf D _ i).symm

def pullback :
    (ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B)) → ℤ) →+
      (ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n J B)) → ℤ) where
  toFun a c := a (componentMap R κ n J B v hpos hneg hsupport hJ hf D c)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pullback_indicator (i : D.Index) :
    pullback R κ n J B v hpos hneg hsupport hJ hf D
      (fun c => @ite ℤ (c = sourceComponent R κ n J B v hpos hneg hsupport hJ D i)
        (Classical.propDecidable _) 1 0)
      (ConnectedComponents.mk (RostComponentEvaluation.point L eJ j)) =
    @ite ℤ (BranchComponentPullback.sourcePoint t L
      ((AdjacentStratumLocalization.targetEquiv A (Fin n) xs J v).toRingEquiv.trans eJ) j
      (OriginalRemainingExtension.extension R κ n J B v hpos hneg hsupport hJ hf) ∈
        Set.range (StratumComponents.componentMap D.Factor D.equiv.toRingEquiv i))
        (Classical.propDecidable _) 1 0 := by
  classical
  change (if componentMap R κ n J B v hpos hneg hsupport hJ hf D
    (ConnectedComponents.mk (RostComponentEvaluation.point L eJ j)) =
      sourceComponent R κ n J B v hpos hneg hsupport hJ D i then (1:ℤ) else 0) = _
  rw [← branch_component_iff R κ n J B v hpos hneg hsupport hJ hf D L eJ j i]

#print axioms SourceFactor
#print axioms sourceEquiv
#print axioms coefficientComponents
#print axioms coefficientComponents_mk
#print axioms closedEquiv_eq_target
#print axioms closedExtension
#print axioms closedExtension_generator
#print axioms componentMap
#print axioms componentMap_mk
#print axioms sourceComponent
#print axioms componentMap_iff
#print axioms branch_sourcePoint
#print axioms branch_component_iff
#print axioms pullback
#print axioms pullback_indicator
end Verification.OriginalBoundaryComponentMap
