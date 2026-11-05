/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFlagArrow
import Verification.PrincipalObjectPurity
import Verification.ActualFlagRegular

/-!
# Actual Flag Principal Maps

The literal coordinate-flag equivalences are exactly the canonical
principal open/closed maps used by purity naturality. This connects the
fixed principal comparison with the original transverse exchange pair.
-/
noncomputable section
namespace Verification.ActualFlagPrincipalMaps
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex
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
local notation "W" => CoordinateFlag.ClosedOld (BasicOpen R κ n J B) (Selected n J) (selectedCoordinate R κ n J B) v
local notation "W'" => Intermediate R (Selected n J) (Other n J ⊕ κ) (Other n J) Sum.inl (matrix κ n J B) v
local notation "a" => CoordinateFlag.parameter (BasicOpen R κ n J B) (Selected n J) (selectedCoordinate R κ n J B) v
local notation "b" => originalParameter R (Selected n J) (Other n J ⊕ κ) (Other n J) Sum.inl (matrix κ n J B) v

theorem openMap_eq : PrincipalPairMaps.openMap R W W' a b
    (ActualCoordinateFlag.intermediateEquiv R κ n J B v).toAlgHom
    (ActualCoordinateFlag.intermediateEquiv_parameter R κ n J B v) =
      (ActualCoordinateFlag.openEquiv R κ n J B v).toAlgHom := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  apply RingHom.ext
  intro z
  exact (PrincipalPairMaps.open_coefficient R W W' a b
    (ActualCoordinateFlag.intermediateEquiv R κ n J B v).toAlgHom
    (ActualCoordinateFlag.intermediateEquiv_parameter R κ n J B v) z).trans
    (ActualCoordinateFlag.openEquiv_algebraMap R κ n J B v z).symm

theorem closedMap_eq : PrincipalPairMaps.closedMap R W W' a b
    (ActualCoordinateFlag.intermediateEquiv R κ n J B v).toAlgHom
    (ActualCoordinateFlag.intermediateEquiv_parameter R κ n J B v) =
      (ActualCoordinateFlag.closedEquiv R κ n J B v).toAlgHom := by
  apply AlgHom.ext
  intro z
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory C)

theorem coneMap_eq : PrincipalPurityInterface.pairConeMap R F W W' a b
    (ActualCoordinateFlag.intermediateEquiv R κ n J B v).toAlgHom
    (ActualCoordinateFlag.intermediateEquiv_parameter R κ n J B v) =
      (ActualFlagArrow.coneIso R κ n J B v F).inv := by
  simp only [PrincipalPurityInterface.pairConeMap,openMap_eq]
  rfl

omit [HasBinaryBiproducts C] in
theorem closedTheory_eq : PrincipalPurityInterface.closedTheoryMap R T W W' a b
    (ActualCoordinateFlag.intermediateEquiv R κ n J B v).toAlgHom
    (ActualCoordinateFlag.intermediateEquiv_parameter R κ n J B v) =
      (T.mapIso (ActualCoordinateFlag.closedEquiv R κ n J B v).toUnder.op).hom := by
  simp only [PrincipalPurityInterface.closedTheoryMap,closedMap_eq,Functor.mapIso_hom]
  rfl

#print axioms openMap_eq
#print axioms closedMap_eq
#print axioms coneMap_eq
#print axioms closedTheory_eq
end Verification.ActualFlagPrincipalMaps
