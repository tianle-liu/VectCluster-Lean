/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRemainingExtension
import Verification.BoundaryComponentSelector

/-!
# Original Boundary Unit Extensions

Actual source coefficients and coordinate selectors on an adjacent
boundary chart. The maps in every equality are the constructed ring maps
from the original exchange presentation.
-/
noncomputable section
namespace Verification.OriginalBoundaryUnitExtensions
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
open Verification.OriginalFreeTorusCoordinates
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : J)
local notation "I" => J.erase v.val
local notation "W" => OriginalBoundaryBranches.Ambient R κ n J B v
local notation "t" => OriginalBoundaryBranches.parameter R κ n J B v
local notation "S" => RemainingRing R κ n (J.erase v.val) B
local notation "Q" => GlobalNormalFrame.ZeroLayer R κ n (J.erase v.val) B
def sourceEquiv : Q ≃+* Localization.Away t :=
  (AdjacentStratumLocalization.sourceEquiv (Global R κ n B) (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) J v).toRingEquiv
local notation "e" => sourceEquiv R κ n J B v

theorem open_coordinate (a : Fin n ⊕ κ) :
    e (ExplicitStratumCoordinates.original R κ n I B a) =
      algebraMap W (Localization.Away t) (OriginalBoundaryBranches.coordinate R κ n J B v a) :=
  AdjacentStratumLocalization.source_original (Global R κ n B) (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) J v (initial R κ n B a)

theorem open_parameter (u : Qˣ)
    (hu : (u : Q) = ExplicitStratumCoordinates.original R κ n I B (Sum.inl v.val)) :
    (Units.map (e).toMonoidHom u : Localization.Away t) =
      algebraMap W (Localization.Away t) t := by
  change e (u : Q) = _
  rw [hu, open_coordinate, OriginalBoundaryBranches.coordinate_parameter]

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
local notation "inc" => OriginalRemainingCoordinates.inclusion R κ n I B hpos hneg hsupport
  (OriginalRemainingExtension.old_independent κ n J B v hJ)
local notation "f" => OriginalRemainingExtension.extension R κ n J B v hpos hneg hsupport hJ hf

theorem open_coefficient (a : S) :
    e (inc a) = algebraMap W (Localization.Away t) (f a) :=
  (OriginalRemainingExtension.open_extension R κ n J B v hpos hneg hsupport hJ hf a).symm

theorem open_coefficient_unit (u : Sˣ) :
    Units.map (e).toMonoidHom (Units.map (inc).toMonoidHom u) =
      Units.map (algebraMap W (Localization.Away t)).toMonoidHom (Units.map (f).toMonoidHom u) := by
  apply Units.ext
  exact open_coefficient R κ n J B v hpos hneg hsupport hJ hf u

theorem extension_idempotent (a : S) (ha : a * a = a) : f a * f a = f a := by
  rw [← map_mul, ha]

theorem open_selector (a : S) (ha : a * a = a) (u : Qˣ) (b : W)
    (hu : (Units.map (e).toMonoidHom u : Localization.Away t) =
      algebraMap W (Localization.Away t) b) :
    (Units.map (e).toMonoidHom
      (BoundaryComponentSelector.unit (inc a) ((map_mul (inc) a a).symm.trans (congrArg (inc) ha)) u) : Localization.Away t) =
      algebraMap W (Localization.Away t) (BoundaryComponentSelector.element (f a) b) := by
  change e (BoundaryComponentSelector.element (inc a) (u : Q)) = _
  calc
    e (BoundaryComponentSelector.element (inc a) (u : Q)) =
        BoundaryComponentSelector.element (e (inc a)) (e (u : Q)) :=
      BoundaryComponentSelector.map_element (e).toRingHom _ _
    _ = BoundaryComponentSelector.element
        (algebraMap W (Localization.Away t) (f a))
        (algebraMap W (Localization.Away t) b) :=
      congrArg₂ BoundaryComponentSelector.element
        (open_coefficient R κ n J B v hpos hneg hsupport hJ hf a) hu
    _ = _ := (BoundaryComponentSelector.map_element (algebraMap W (Localization.Away t)) _ _).symm

theorem open_parameter_selector (a : S) (ha : a * a = a) (u : Qˣ)
    (hu : (u : Q) = ExplicitStratumCoordinates.original R κ n I B (Sum.inl v.val)) :
    (Units.map (e).toMonoidHom
      (BoundaryComponentSelector.unit (inc a) ((map_mul (inc) a a).symm.trans (congrArg (inc) ha)) u) : Localization.Away t) =
      algebraMap W (Localization.Away t) (BoundaryComponentSelector.element (f a) t) :=
  open_selector R κ n J B v hpos hneg hsupport hJ hf a ha u t
    (open_parameter R κ n J B v u hu)

include hf in
theorem complement_selector_extends (a : S) (ha : a * a = a) (k : Other n J ⊕ κ)
    (u : Qˣ) (hu : (u : Q) = ExplicitStratumCoordinates.original R κ n I B
      (IndependentChartPresentation.complementEmbedding κ n J k)) :
    ∃ w : Wˣ, Units.map (e).toMonoidHom
      (BoundaryComponentSelector.unit (inc a) ((map_mul (inc) a a).symm.trans (congrArg (inc) ha)) u) =
        Units.map (algebraMap W (Localization.Away t)).toMonoidHom w := by
  let x := (OriginalBoundaryBranches.complement_unit R κ n J B v k).unit
  refine ⟨BoundaryComponentSelector.unit (f a)
    (extension_idempotent R κ n J B v hpos hneg hsupport hJ hf a ha) x, ?_⟩
  apply Units.ext
  change _ = algebraMap W (Localization.Away t) (BoundaryComponentSelector.element (f a) (x : W))
  rw [show (x : W) = OriginalBoundaryBranches.coordinate R κ n J B v
    (IndependentChartPresentation.complementEmbedding κ n J k) from IsUnit.unit_spec _]
  apply open_selector R κ n J B v hpos hneg hsupport hJ hf a ha u
  change e (u : Q) = _
  rw [hu, open_coordinate]

#print axioms sourceEquiv
#print axioms open_coordinate
#print axioms open_parameter
#print axioms open_coefficient
#print axioms open_coefficient_unit
#print axioms extension_idempotent
#print axioms open_selector
#print axioms open_parameter_selector
#print axioms complement_selector_extends
end Verification.OriginalBoundaryUnitExtensions
