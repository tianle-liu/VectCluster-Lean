/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmoothPartialConormal
import Verification.IndependentCoordinatePurity
import Verification.ActualFlagRegular

/-!
# Old Coordinate Frame

Every old-coordinate pair inside an actual independent J-chart has the
original partial conormal frame. Smoothness, regularity and this basis are
all deduced from AS and the actual parameter map.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OldCoordinateFrame
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (J : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)))
variable (v : Selected n J)

def frame : CoordinatePurityInput.Frame R (BasicOpen R κ n J B)
    (CoordinateFlag.Old (Selected n J) v)
      (CoordinateFlag.oldCoordinate (BasicOpen R κ n J B) (Selected n J)
        (selectedCoordinate R κ n J B) v) := by
  obtain ⟨m,s⟩ := (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)).smithNormalForm Finsupp.basisSingleOne
  have he : ∀ i, IsUnit ((s.a i).natAbs : R) := by
    intro i
    simp only [SaturatedSmith.coefficient_natAbs s hs,Nat.cast_one,isUnit_one]
  letI := GlobalNormalFrame.parameters_smooth R κ n J B hpos hneg hsupport hJ hf s he
  let full := IndependentCoordinatePurity.frame R κ n J B hpos hneg hsupport hJ hf hs
  exact {
    smooth := full.smooth
    closedSmooth := ActualFlagRegular.old_smooth R κ n J B v
      (matrix_zero_block κ n J B hpos hneg hsupport hJ) hf hs
    regular := fun l hl => by
      have h := full.regular (l.map Subtype.val) (hl.map Subtype.val_injective)
      simpa only [List.map_map,CoordinateFlag.oldCoordinate,Function.comp_def] using h
    basis := SmoothPartialConormal.basis R (BasicOpen R κ n J B) (Selected n J)
      {i | i ≠ v} (selectedCoordinate R κ n J B) (GlobalNormalFrame.parameter_X R κ n J B)
    basis_generator := SmoothPartialConormal.basis_apply R (BasicOpen R κ n J B) (Selected n J)
      {i | i ≠ v} (selectedCoordinate R κ n J B) (GlobalNormalFrame.parameter_X R κ n J B) }

#print axioms frame
end Verification.OldCoordinateFrame
