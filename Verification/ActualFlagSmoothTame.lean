/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFlagRegular

/-!
# Actual Flag Smooth Tame

Tame-rank smoothness for each ring of the original adjacent principal
pair. These are derived from the Smith coefficients of the actual selected
columns; saturation is not required.
-/
noncomputable section
namespace Verification.ActualFlagSmoothTame
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
variable {m : ℕ} (s : Basis.SmithNormalForm
  (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)) (Other n J ⊕ κ) m)
variable (he : ∀ i, IsUnit ((s.a i).natAbs : R))
include hB hf s he

theorem old_smooth : Algebra.Smooth R (CoordinateFlag.ClosedOld A Sel x v) := by
  letI := ActualTransverseSmooth.intermediate_smooth_tame R Sel K Rest Sum.inl D v hB hf s he
  exact Algebra.Smooth.of_equiv (ActualCoordinateFlag.intermediateEquiv R κ n J B v).symm

theorem closed_smooth : Algebra.Smooth R (CoordinateFlag.ClosedAll A Sel x v) := by
  letI := ActualTransversePairSmooth.closed_smooth_tame R Sel K Rest Sum.inl D hB hf s he v
  exact Algebra.Smooth.of_equiv (ActualCoordinateFlag.closedEquiv R κ n J B v).symm

theorem open_smooth : Algebra.Smooth R (CoordinateFlag.OpenOld A Sel x v) := by
  letI := old_smooth R κ n J B v hB hf s he
  letI : Algebra.Smooth (CoordinateFlag.ClosedOld A Sel x v)
    (CoordinateFlag.OpenOld A Sel x v) :=
      Algebra.Smooth.of_isLocalization_Away (CoordinateFlag.parameter A Sel x v)
  exact Algebra.Smooth.comp R (CoordinateFlag.ClosedOld A Sel x v) _

#print axioms old_smooth
#print axioms closed_smooth
#print axioms open_smooth
end Verification.ActualFlagSmoothTame
