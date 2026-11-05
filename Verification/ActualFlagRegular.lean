/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualCoordinateFlag
import Verification.ActualTransversePairSmooth

/-!
# Actual Flag Regular

The literal old-coordinate closed subscheme has the expected regular
last original parameter. AS smoothness and the original conormal generator
transport along the proved actual flag identifications.
-/
noncomputable section
namespace Verification.ActualFlagRegular
set_option synthInstance.maxHeartbeats 100000
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.ActualTransverseSlice
open Verification.ActualTransverseLocalization
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
local notation "A" => BasicOpen R κ n J B
local notation "Sel" => Selected n J
local notation "K" => Other n J ⊕ κ
local notation "Rest" => Other n J
local notation "D" => matrix κ n J B
local notation "x" => selectedCoordinate R κ n J B
variable (hB : ∀ l i : Selected n J, (matrix κ n J B) (Sum.inl l) (Sum.inl i) = 0)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))

include hB hf in
theorem parameter_regular : IsSMulRegular (CoordinateFlag.ClosedOld A Sel x v)
    (CoordinateFlag.parameter A Sel x v) := by
  have hreg := ActualTransverseRegular.parameter_regular R Sel K Rest Sum.inl D hB hf v
  intro a b hab
  apply (ActualCoordinateFlag.intermediateEquiv R κ n J B v).injective
  apply hreg
  change originalParameter R Sel K Rest Sum.inl D v * _ =
    originalParameter R Sel K Rest Sum.inl D v * _
  rw [← ActualCoordinateFlag.intermediateEquiv_parameter R κ n J B v, ← map_mul, ← map_mul]
  exact congrArg (ActualCoordinateFlag.intermediateEquiv R κ n J B v) hab

include hB hf in
theorem old_smooth (hs : FreezingLattice.Saturated (LinearMap.range
    (GlobalExchangeSmooth.selectedMap κ n B J))) :
    Algebra.Smooth R (CoordinateFlag.ClosedOld A Sel x v) := by
  letI := ActualTransverseSmooth.intermediate_smooth_AS R Sel K Rest Sum.inl D v hB hf hs
  exact Algebra.Smooth.of_equiv (ActualCoordinateFlag.intermediateEquiv R κ n J B v).symm

include hB hf in
theorem closed_smooth (hs : FreezingLattice.Saturated (LinearMap.range
    (GlobalExchangeSmooth.selectedMap κ n B J))) :
    Algebra.Smooth R (CoordinateFlag.ClosedAll A Sel x v) := by
  letI := (ActualTransversePairSmooth.pair_smooth_AS R Sel K Rest Sum.inl D hB hf hs v).2.2
  exact Algebra.Smooth.of_equiv (ActualCoordinateFlag.closedEquiv R κ n J B v).symm

def conormalBasis : Basis PUnit.{1} (CoordinateFlag.ClosedAll A Sel x v)
    (CoordinateFlag.finalIdeal A Sel x v).Cotangent :=
  PrincipalConormal.basis (CoordinateFlag.parameter A Sel x v)
    (parameter_regular R κ n J B v hB hf)

theorem conormalBasis_apply (i : PUnit.{1}) :
    conormalBasis R κ n J B v hB hf i =
      (CoordinateFlag.finalIdeal A Sel x v).toCotangent
        ⟨CoordinateFlag.parameter A Sel x v, Ideal.subset_span (Set.mem_singleton _)⟩ :=
  PrincipalConormal.basis_apply _ _ i

def conormalMap : (CoordinateFlag.finalIdeal A Sel x v).Cotangent →ₗ[R]
    (closedIdeal R Sel K Rest Sum.inl D v).Cotangent :=
  Ideal.mapCotangent _ _ (ActualCoordinateFlag.intermediateEquiv R κ n J B v).toAlgHom
    (Ideal.map_le_iff_le_comap.mp (le_of_eq (ActualCoordinateFlag.finalIdeal_map R κ n J B v)))

theorem conormalMap_frame :
    conormalMap R κ n J B v (conormalBasis R κ n J B v hB hf PUnit.unit) =
      (closedIdeal R Sel K Rest Sum.inl D v).toCotangent
        ⟨originalParameter R Sel K Rest Sum.inl D v, Ideal.subset_span (Set.mem_singleton _)⟩ := by
  rw [conormalBasis_apply, conormalMap, Ideal.mapCotangent_toCotangent]
  apply congrArg (closedIdeal R Sel K Rest Sum.inl D v).toCotangent
  apply Subtype.ext
  exact ActualCoordinateFlag.intermediateEquiv_parameter R κ n J B v

#print axioms parameter_regular
#print axioms old_smooth
#print axioms closed_smooth
#print axioms conormalBasis
#print axioms conormalBasis_apply
#print axioms conormalMap
#print axioms conormalMap_frame
end Verification.ActualFlagRegular
