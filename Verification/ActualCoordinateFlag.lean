/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateFlag
import Verification.IndependentOpenCoordinates
import Verification.ActualTransverseClosed

/-!
# Actual Coordinate Flag

The coordinate flag inside the actual complementary basic open is
the literal transverse intermediate exchange chart. All quotient and
principal-localization maps commute and the surviving original parameter
is preserved exactly. No purity comparison is assumed here.
-/
noncomputable section
namespace Verification.ActualCoordinateFlag
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

theorem oldIdeal_map :
    (CoordinateFlag.oldIdeal A Sel x v).map (chartEquiv R κ n J B).toRingHom =
      partialIdeal R Sel K Rest Sum.inl D v := by
  unfold CoordinateFlag.oldIdeal ConormalFrame.ideal partialIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact chartEquiv_selectedCoordinate R κ n J B i.val

def intermediateEquiv : CoordinateFlag.ClosedOld A Sel x v ≃ₐ[R]
    Intermediate R Sel K Rest Sum.inl D v :=
  Ideal.quotientEquivAlg _ _ (chartEquiv R κ n J B) (oldIdeal_map R κ n J B v).symm

theorem intermediateEquiv_mk (a : A) :
    intermediateEquiv R κ n J B v (Ideal.Quotient.mk (CoordinateFlag.oldIdeal A Sel x v) a) =
      Ideal.Quotient.mk (partialIdeal R Sel K Rest Sum.inl D v) (chartEquiv R κ n J B a) := rfl

theorem intermediateEquiv_parameter :
    intermediateEquiv R κ n J B v (CoordinateFlag.parameter A Sel x v) =
      originalParameter R Sel K Rest Sum.inl D v := by
  rw [CoordinateFlag.parameter, intermediateEquiv_mk, chartEquiv_selectedCoordinate]
  rfl

theorem map_parameterPowers :
    (Submonoid.powers (CoordinateFlag.parameter A Sel x v)).map
      (intermediateEquiv R κ n J B v).toMonoidHom =
        Submonoid.powers (originalParameter R Sel K Rest Sum.inl D v) := by
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (intermediateEquiv_parameter R κ n J B v)

def openEquiv : CoordinateFlag.OpenOld A Sel x v ≃ₐ[R] OpenSource R Sel K Rest Sum.inl D v :=
  IsLocalization.algEquivOfAlgEquiv _ _ (intermediateEquiv R κ n J B v)
    (map_parameterPowers R κ n J B v)

theorem openEquiv_algebraMap (a : CoordinateFlag.ClosedOld A Sel x v) :
    openEquiv R κ n J B v (algebraMap (CoordinateFlag.ClosedOld A Sel x v)
      (CoordinateFlag.OpenOld A Sel x v) a) =
    algebraMap (Intermediate R Sel K Rest Sum.inl D v) (OpenSource R Sel K Rest Sum.inl D v)
      (intermediateEquiv R κ n J B v a) :=
  IsLocalization.map_eq
    (M := Submonoid.powers (CoordinateFlag.parameter A Sel x v))
    (T := Submonoid.powers (originalParameter R Sel K Rest Sum.inl D v))
    (S := CoordinateFlag.OpenOld A Sel x v) (Q := OpenSource R Sel K Rest Sum.inl D v)
    (g := (intermediateEquiv R κ n J B v).toRingHom)
    (Submonoid.le_comap_of_map_le _ (le_of_eq (map_parameterPowers R κ n J B v))) a

theorem openEquiv_parameter :
    openEquiv R κ n J B v
      (algebraMap (CoordinateFlag.ClosedOld A Sel x v) (CoordinateFlag.OpenOld A Sel x v)
        (CoordinateFlag.parameter A Sel x v)) =
    algebraMap (Intermediate R Sel K Rest Sum.inl D v) (OpenSource R Sel K Rest Sum.inl D v)
      (originalParameter R Sel K Rest Sum.inl D v) := by
  rw [openEquiv_algebraMap, intermediateEquiv_parameter]

theorem finalIdeal_map :
    (CoordinateFlag.finalIdeal A Sel x v).map (intermediateEquiv R κ n J B v).toRingHom =
      closedIdeal R Sel K Rest Sum.inl D v := by
  rw [CoordinateFlag.finalIdeal, Ideal.map_span, Set.image_singleton]
  exact congrArg (fun z => Ideal.span ({z} : Set _)) (intermediateEquiv_parameter R κ n J B v)

def closedEquiv : CoordinateFlag.ClosedAll A Sel x v ≃ₐ[R] ClosedSource R Sel K Rest Sum.inl D v :=
  Ideal.quotientEquivAlg _ _ (intermediateEquiv R κ n J B v) (finalIdeal_map R κ n J B v).symm

theorem closedEquiv_mk (a : CoordinateFlag.ClosedOld A Sel x v) :
    closedEquiv R κ n J B v (Ideal.Quotient.mk (CoordinateFlag.finalIdeal A Sel x v) a) =
      Ideal.Quotient.mk (closedIdeal R Sel K Rest Sum.inl D v) (intermediateEquiv R κ n J B v a) := rfl

theorem open_square :
    (openEquiv R κ n J B v).toAlgHom.comp
      (IsScalarTower.toAlgHom R (CoordinateFlag.ClosedOld A Sel x v) (CoordinateFlag.OpenOld A Sel x v)) =
    (IsScalarTower.toAlgHom R (Intermediate R Sel K Rest Sum.inl D v) (OpenSource R Sel K Rest Sum.inl D v)).comp
      (intermediateEquiv R κ n J B v).toAlgHom := by
  apply AlgHom.ext
  exact openEquiv_algebraMap R κ n J B v

theorem closed_square :
    (closedEquiv R κ n J B v).toAlgHom.comp
      (Ideal.Quotient.mkₐ R (CoordinateFlag.finalIdeal A Sel x v)) =
    (Ideal.Quotient.mkₐ R (closedIdeal R Sel K Rest Sum.inl D v)).comp
      (intermediateEquiv R κ n J B v).toAlgHom := rfl

#print axioms oldIdeal_map
#print axioms intermediateEquiv
#print axioms intermediateEquiv_mk
#print axioms intermediateEquiv_parameter
#print axioms map_parameterPowers
#print axioms openEquiv
#print axioms openEquiv_algebraMap
#print axioms openEquiv_parameter
#print axioms finalIdeal_map
#print axioms closedEquiv
#print axioms closedEquiv_mk
#print axioms open_square
#print axioms closed_square
end Verification.ActualCoordinateFlag
