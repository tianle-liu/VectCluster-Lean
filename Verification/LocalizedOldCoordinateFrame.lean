/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OldCoordinateFrame
import Verification.AdjacentChartLocalization
import Verification.CoordinateFlagLocalization
import Verification.GlobalSelectedColumns

/-!
# Localized Old Coordinate Frame

The localized old-coordinate pair has an actual regular conormal frame.
AS is needed only for J: its hereditary lattice consequence supplies the
smaller chart. Localizing the formal parameter map constructs the basis;
regularity is transported through the actual adjacent-chart equivalence.
-/
noncomputable section
namespace Verification.LocalizedOldCoordinateFrame
set_option synthInstance.maxHeartbeats 100000
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.CoordinateFlagLocalization
attribute [local instance] MvPolynomial.algebraMvPolynomial RingHomInvPair.of_ringEquiv
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (J : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (v : Selected n J)
local notation "A" => BasicOpen R κ n J B
local notation "Sel" => Selected n J
local notation "x" => selectedCoordinate R κ n J B
local notation "S" => Ambient A Sel x v
local notation "y" => coordinate A Sel x v

def indexEquiv : CoordinateFlag.Old Sel v ≃ Selected n (J.erase v.val) where
  toFun i := ⟨i.val.val, Finset.mem_erase.mpr ⟨fun h => i.property (Subtype.ext h),i.val.property⟩⟩
  invFun i := ⟨⟨i.val,(Finset.mem_erase.mp i.property).2⟩,
    fun h => (Finset.mem_erase.mp i.property).1 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def chartEquiv : S ≃ₐ[R] BasicOpen R κ n (J.erase v.val) B :=
  (AdjacentChartLocalization.equiv (fun i => initial R κ n B (Sum.inl i)) J v).restrictScalars R

omit [Nontrivial R] in
theorem chartEquiv_coordinate (i : CoordinateFlag.Old Sel v) :
    chartEquiv R κ n J B v (y i) =
    selectedCoordinate R κ n (J.erase v.val) B (indexEquiv n J v i) := by
  change chartEquiv R κ n J B v
    (algebraMap A S (algebraMap (Global R κ n B) A (initial R κ n B (Sum.inl i.val.val)))) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact (AdjacentChartLocalization.equiv (fun i => initial R κ n B (Sum.inl i)) J v).commutes _

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)))

include hf hs in
omit [Nontrivial R] in
theorem erase_injective : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B (J.erase v.val)) := by
  exact ((GlobalSelectedColumns.AS_iff κ n B (J.erase v.val)).mpr
    (AnticliqueSubcolumns.AS_subset (fun a i => B a (Sum.inl i)) (Finset.erase_subset _ _)
      ((GlobalSelectedColumns.AS_iff κ n B J).mp ⟨hf,hs⟩))).1

include hpos hneg hsupport hJ hf hs in
theorem regular (l : List (CoordinateFlag.Old Sel v)) (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular S (l.map y) := by
  let e := (chartEquiv R κ n J B v).toRingEquiv
  apply (e.toSemilinearEquiv.isRegular_congr' (l.map y)).mpr
  have hm : (l.map y).map e.toRingHom =
      (l.map (indexEquiv n J v)).map (selectedCoordinate R κ n (J.erase v.val) B) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    exact chartEquiv_coordinate R κ n J B v i
  change RingTheory.Sequence.IsRegular (BasicOpen R κ n (J.erase v.val) B) ((l.map y).map e.toRingHom)
  rw [hm]
  exact GlobalRegularParameters.selected_coordinates_regular R κ n B hpos hneg hsupport
    (J.erase v.val) (fun i hi j hj => hJ i (Finset.erase_subset _ _ hi) j (Finset.erase_subset _ _ hj))
    (erase_injective κ n J B v hf hs) _ (hl.map (indexEquiv n J v).injective)

def frame : CoordinatePurityInput.Frame R S (CoordinateFlag.Old Sel v) y := by
  obtain ⟨m,s⟩ := (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)).smithNormalForm Finsupp.basisSingleOne
  have he : ∀ i, IsUnit ((s.a i).natAbs : R) := by
    intro i
    simp only [SaturatedSmith.coefficient_natAbs s hs,Nat.cast_one,isUnit_one]
  let old := OldCoordinateFrame.frame R κ n J B hpos hneg hsupport hJ hf hs v
  letI : Algebra.Smooth R A := old.smooth
  letI : Algebra.Smooth A S := Algebra.Smooth.of_isLocalization_Away (x v)
  letI : Algebra.Smooth R (CoordinateFlag.ClosedOld A Sel x v) := old.closedSmooth
  letI : Algebra.Smooth (CoordinateFlag.ClosedOld A Sel x v) (CoordinateFlag.OpenOld A Sel x v) :=
    Algebra.Smooth.of_isLocalization_Away (CoordinateFlag.parameter A Sel x v)
  letI : Algebra.Smooth R (CoordinateFlag.OpenOld A Sel x v) :=
    Algebra.Smooth.comp R (CoordinateFlag.ClosedOld A Sel x v) _
  letI := GlobalNormalFrame.parameters_smooth R κ n J B hpos hneg hsupport hJ hf s he
  letI : Algebra.Smooth (MvPolynomial Sel R) S := Algebra.Smooth.comp (MvPolynomial Sel R) A S
  have hx : ∀ i : Sel, algebraMap (MvPolynomial Sel R) S (MvPolynomial.X i) = algebraMap A S (x i) := by
    intro i
    rw [IsScalarTower.algebraMap_apply (MvPolynomial Sel R) A S,GlobalNormalFrame.parameter_X]
  exact {
    smooth := Algebra.Smooth.comp R A S
    closedSmooth := Algebra.Smooth.of_equiv (closedEquiv R A Sel x v).symm
    regular := regular R κ n J B v hpos hneg hsupport hJ hf hs
    basis := SmoothPartialConormal.basis R S Sel {i | i ≠ v} (fun i => algebraMap A S (x i)) hx
    basis_generator := SmoothPartialConormal.basis_apply R S Sel {i | i ≠ v} (fun i => algebraMap A S (x i)) hx }

#print axioms indexEquiv
#print axioms chartEquiv
#print axioms chartEquiv_coordinate
#print axioms erase_injective
#print axioms regular
#print axioms frame
end Verification.LocalizedOldCoordinateFrame
