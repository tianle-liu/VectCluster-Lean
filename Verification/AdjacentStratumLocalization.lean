/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostSupportDivisorInput
import Verification.CoordinateFlagLocalization
import Verification.CoordinateFlagTotalQuotient

/-!
# Adjacent Stratum Localization

Adjacent coordinate strata are the actual open/closed pair in the
old-coordinate quotient of the complementary chart. All equivalences
are over the original ring, and hence retain every ambient function.
-/
noncomputable section
namespace Verification.AdjacentStratumLocalization
open scoped BigOperators
open Verification.PrimeStratumPresentation
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (J : Finset V) (v : J)
local notation "C" => OpenRing x J
def coordinate (i : J) : C := algebraMap A C (x i.val)
local notation "xs" => coordinate A V x J

abbrev DoubleOpen := Localization.Away (algebraMap A C (x v.val))

theorem complement_product : (∏ i ∈ (J.erase v.val)ᶜ, x i) =
    x v.val * ∏ i ∈ Jᶜ, x i := by
  rw [Finset.compl_erase, Finset.prod_insert (Finset.not_mem_compl.mpr v.property)]

instance doubleLocalization : IsLocalization.Away (∏ i ∈ (J.erase v.val)ᶜ, x i)
    (DoubleOpen A V x J v) := by
  rw [complement_product]
  exact IsLocalization.Away.mul C (DoubleOpen A V x J v) (∏ i ∈ Jᶜ, x i) (x v.val)

def openEquiv : OpenRing x (J.erase v.val) ≃ₐ[A] DoubleOpen A V x J v :=
  IsLocalization.algEquiv (Submonoid.powers (∏ i ∈ (J.erase v.val)ᶜ, x i)) _ _

theorem openEquiv_coordinate (i : V) :
    openEquiv A V x J v (algebraMap A (OpenRing x (J.erase v.val)) (x i)) =
      algebraMap A (DoubleOpen A V x J v) (x i) :=
  (openEquiv A V x J v).commutes _

theorem oldIdeal_map : (zeroIdeal x (J.erase v.val)).map
    (openEquiv A V x J v).toRingHom =
      ConormalFrame.ideal (CoordinateFlagLocalization.coordinate C J xs v) := by
  rw [zeroIdeal, Ideal.map_span, ← Set.range_comp]
  unfold ConormalFrame.ideal
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    have hi := Finset.mem_erase.mp i.property
    refine ⟨⟨⟨i.val, hi.2⟩, fun h => hi.1 (congrArg Subtype.val h)⟩, ?_⟩
    change algebraMap C (DoubleOpen A V x J v) (algebraMap A C (x i.val)) =
      openEquiv A V x J v (algebraMap A (OpenRing x (J.erase v.val)) (x i.val))
    rw [openEquiv_coordinate, ← IsScalarTower.algebraMap_apply]
  · rintro ⟨i, rfl⟩
    have hi : i.val.val ≠ v.val := fun h => i.property (Subtype.ext h)
    refine ⟨⟨i.val.val, Finset.mem_erase.mpr ⟨hi, i.val.property⟩⟩, ?_⟩
    change openEquiv A V x J v (algebraMap A (OpenRing x (J.erase v.val)) (x i.val.val)) =
      algebraMap C (DoubleOpen A V x J v) (algebraMap A C (x i.val.val))
    rw [openEquiv_coordinate, ← IsScalarTower.algebraMap_apply]

def sourceEquiv : ClosedRing x (J.erase v.val) ≃ₐ[A]
    CoordinateFlag.OpenOld C J xs v :=
  (Ideal.quotientEquivAlg _ _ (openEquiv A V x J v) (oldIdeal_map A V x J v).symm).trans
    (CoordinateFlagLocalization.closedEquiv A C J xs v)

def targetEquiv : CoordinateFlag.ClosedAll C J xs v ≃ₐ[A] ClosedRing x J :=
  CoordinateFlagTotalQuotient.equiv A C J xs v

def coordinates : RostSupportDivisorInput.Coordinates A V x (J.erase v.val) J v where
  source := sourceEquiv A V x J v
  target := targetEquiv A V x J v

theorem source_original (a : A) :
    sourceEquiv A V x J v (algebraMap A (ClosedRing x (J.erase v.val)) a) =
      algebraMap A (CoordinateFlag.OpenOld C J xs v) a :=
  (sourceEquiv A V x J v).commutes a

theorem target_original (a : A) :
    targetEquiv A V x J v (algebraMap A (CoordinateFlag.ClosedAll C J xs v) a) =
      algebraMap A (ClosedRing x J) a :=
  (targetEquiv A V x J v).commutes a

#print axioms coordinate
#print axioms DoubleOpen
#print axioms complement_product
#print axioms doubleLocalization
#print axioms openEquiv
#print axioms openEquiv_coordinate
#print axioms oldIdeal_map
#print axioms sourceEquiv
#print axioms targetEquiv
#print axioms coordinates
#print axioms source_original
#print axioms target_original
end Verification.AdjacentStratumLocalization
