/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ReducedBoundaryBranchOrder
import Verification.ActualFlagRegular
import Verification.CoordinateFlagTotalQuotient
import Verification.OriginalRetainedStratumUnits

/-!
# Original Boundary Branches

Multiplicity one at every actual connected boundary component, under
AR rather than the stronger saturated condition. The old coordinate
quotient and its last equation are literal original coordinates. Local
integrality is proved from regularity; no branch-domain premise is added.
-/
noncomputable section
namespace Verification.OriginalBoundaryBranches
open Verification.IndependentChartIndex Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.FrozenAcyclicCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)

abbrev Ambient := CoordinateFlag.ClosedOld (BasicOpen R κ n J B) (Selected n J)
  (selectedCoordinate R κ n J B) v

local instance ambientSelfSMul : SMul (Ambient R κ n J B v) (Ambient R κ n J B v) :=
  ⟨fun a b => a * b⟩

def parameter : Ambient R κ n J B v := CoordinateFlag.parameter
  (BasicOpen R κ n J B) (Selected n J) (selectedCoordinate R κ n J B) v

def closedEquiv : (Ambient R κ n J B v ⧸ Ideal.span {parameter R κ n J B v}) ≃+*
    GlobalNormalFrame.ZeroLayer R κ n J B :=
  (CoordinateFlagTotalQuotient.equiv R (BasicOpen R κ n J B) (Selected n J)
    (selectedCoordinate R κ n J B) v).toRingEquiv

def coordinate (a : Fin n ⊕ κ) : Ambient R κ n J B v :=
  Ideal.Quotient.mk (CoordinateFlag.oldIdeal (BasicOpen R κ n J B) (Selected n J)
    (selectedCoordinate R κ n J B) v)
    (algebraMap (Global R κ n B) (BasicOpen R κ n J B) (initial R κ n B a))

theorem coordinate_parameter : coordinate R κ n J B v (Sum.inl v.val) =
    parameter R κ n J B v := rfl

theorem complement_unit (a : Other n J ⊕ κ) :
    IsUnit (coordinate R κ n J B v
      (IndependentChartPresentation.complementEmbedding κ n J a)) :=
  (IndependentBasicOpen.complement_units R κ n J B a).map (Ideal.Quotient.mk
    (CoordinateFlag.oldIdeal (BasicOpen R κ n J B) (Selected n J)
      (selectedCoordinate R κ n J B) v))

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable {m : ℕ} (s : Basis.SmithNormalForm
  (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)) (Other n J ⊕ κ) m)
variable (he : ∀ i, IsUnit ((s.a i).natAbs : R))

include hpos hneg hsupport hJ hf in
theorem parameter_regular : IsSMulRegular (Ambient R κ n J B v) (parameter R κ n J B v) :=
  ActualFlagRegular.parameter_regular R κ n J B v
    (matrix_zero_block κ n J B hpos hneg hsupport hJ) hf

include hpos hneg hsupport hJ hf s he in
theorem ambient_noetherian : IsNoetherianRing (Ambient R κ n J B v) := by
  letI := GlobalExchangeSmooth.basicOpen_smooth R κ n B hpos hneg hsupport J hJ hf s he
  letI := Algebra.FiniteType.isNoetherianRing R (BasicOpen R κ n J B)
  infer_instance

include hpos hneg hsupport hJ hf s he in
theorem branch_orders :
    ∃ (T : Type) (_ : Finite T) (D : T → Type) (_ : ∀ t, CommRing (D t))
      (_ : ∀ t, IsDomain (D t))
      (e : (Ambient R κ n J B v ⧸ Ideal.span {parameter R κ n J B v}) ≃+* ∀ t, D t)
      (ν : T → AddValuation (Ambient R κ n J B v) ℕ∞),
      (∀ t, ν t (parameter R κ n J B v) = 1) ∧
      (∀ t a, e (Ideal.Quotient.mk _ a) t ≠ 0 → ν t a = 0) ∧
      (∀ t (a : Other n J ⊕ κ), ν t (coordinate R κ n J B v
        (IndependentChartPresentation.complementEmbedding κ n J a)) = 0) ∧
      (∀ t (q : PrimeSpectrum (D t)),
        connectedComponent (StratumComponents.componentMap D e t q) =
          Set.range (StratumComponents.componentMap D e t)) := by
  classical
  obtain ⟨T, hT, L, hL, aL, K, hK, E, _, _, _⟩ :=
    OriginalRetainedStratumUnits.component_units R κ n J B hpos hneg hsupport hJ hf s he
  letI := hT
  letI := hL
  letI := aL
  letI := hK
  let D : T → Type := fun t => MvPolynomial (Selected n J)
    (OriginalTorus.Torus (OriginalTorus.Torus (L t) K)
      (OriginalFreeTorusCoordinates.FreeIndex κ n J B))
  let e := (closedEquiv R κ n J B v).trans E
  letI := ambient_noetherian R κ n J B v hpos hneg hsupport hJ hf s he
  have hx := parameter_regular R κ n J B v hpos hneg hsupport hJ hf
  refine ⟨T, hT, D, (fun _ => inferInstance), (fun _ => inferInstance), e,
    (fun t => ReducedBoundaryBranchOrder.order _ _ D e t hx), ?_, ?_, ?_, ?_⟩
  · exact fun t => ReducedBoundaryBranchOrder.order_parameter _ _ D e t hx
  · intro t a ha
    apply ReducedBoundaryBranchOrder.order_not_mem _ _ D e t hx
    exact (ReducedBoundaryBranchOrder.mem_branch _ _ D e t a).not.mpr ha
  · intro t a
    apply ReducedBoundaryBranchOrder.order_not_mem _ _ D e t hx
    exact ((complement_unit R κ n J B v a).map
      (ReducedBoundaryBranchOrder.projection _ _ D e t)).ne_zero
  · exact fun t q => StratumComponents.componentMap_component D e t q

#print axioms Ambient
#print axioms ambientSelfSMul
#print axioms parameter
#print axioms closedEquiv
#print axioms coordinate
#print axioms coordinate_parameter
#print axioms complement_unit
#print axioms parameter_regular
#print axioms ambient_noetherian
#print axioms branch_orders
end Verification.OriginalBoundaryBranches
