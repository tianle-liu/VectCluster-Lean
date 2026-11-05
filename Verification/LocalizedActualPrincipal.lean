/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFlagPrincipalMaps
import Verification.ActualPrincipalObjectPurity
import Verification.LocalizedPrincipalPurity

/-!
# Localized Actual Principal

Fixed principal-purity comparisons are transported through the actual
coordinate flag equivalences. The smoothness and regularity premises
are proved for the original exchange chart under AS.
-/
noncomputable section
namespace Verification.LocalizedActualPrincipal
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.ActualTransverseSlice
open Verification.ActualTransverseLocalization
universe w
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
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)))
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {Z : Type*} [Category Z]
variable (L : DerivedCategory C ⥤ Z)
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ Z)
variable (P : LocalizedPrincipalPurity.Standard L R F T)

def ambientIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R)
    (ClosedSource R Sel K Rest Sum.inl D v))) ≅
    L.obj (DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.ambientOpen R Sel K Rest Sum.inl D v F))) :=
  P.comparison (Intermediate R Sel K Rest Sum.inl D v) (originalParameter R Sel K Rest Sum.inl D v)
    (ActualTransverseSmooth.intermediate_smooth_AS R Sel K Rest Sum.inl D v hB hf hs)
    (ActualTransversePairSmooth.pair_smooth_AS R Sel K Rest Sum.inl D hB hf hs v).2.2
    (ActualTransverseRegular.parameter_regular R Sel K Rest Sum.inl D hB hf v)

def flagIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (CoordinateFlag.ClosedAll A Sel x v))) ≅
    L.obj (DerivedCategory.Q.obj (mappingCone (ActualFlagArrow.oldArrow R κ n J B v F))) :=
  P.comparison (CoordinateFlag.ClosedOld A Sel x v) (CoordinateFlag.parameter A Sel x v)
    (ActualFlagRegular.old_smooth R κ n J B v hB hf hs)
    (ActualFlagRegular.closed_smooth R κ n J B v hB hf hs)
    (ActualFlagRegular.parameter_regular R κ n J B v hB hf)

theorem comparison_square : (T.mapIso (ActualCoordinateFlag.closedEquiv R κ n J B v).toUnder.op).hom ≫
    (flagIso R κ n J B v hB hf hs L F T P).hom =
      (ambientIso R κ n J B v hB hf hs L F T P).hom ≫
        L.map (ActualFlagArrow.coneIso R κ n J B v F).inv := by
  have h := P.naturality (CoordinateFlag.ClosedOld A Sel x v) (Intermediate R Sel K Rest Sum.inl D v)
    (CoordinateFlag.parameter A Sel x v) (originalParameter R Sel K Rest Sum.inl D v)
    (ActualCoordinateFlag.intermediateEquiv R κ n J B v).toAlgHom
    (ActualCoordinateFlag.intermediateEquiv_parameter R κ n J B v)
    (ActualFlagRegular.old_smooth R κ n J B v hB hf hs)
    (ActualFlagRegular.closed_smooth R κ n J B v hB hf hs)
    (ActualTransverseSmooth.intermediate_smooth_AS R Sel K Rest Sum.inl D v hB hf hs)
    (ActualTransversePairSmooth.pair_smooth_AS R Sel K Rest Sum.inl D hB hf hs v).2.2
    (ActualFlagRegular.parameter_regular R κ n J B v hB hf)
    (ActualTransverseRegular.parameter_regular R Sel K Rest Sum.inl D hB hf v)
  rw [ActualFlagPrincipalMaps.closedMap_eq,ActualFlagPrincipalMaps.coneMap_eq] at h
  exact h

theorem comparison_transport : (flagIso R κ n J B v hB hf hs L F T P).hom ≫
    L.map (ActualFlagArrow.coneIso R κ n J B v F).hom =
      (T.mapIso (ActualCoordinateFlag.closedEquiv R κ n J B v).toUnder.op).inv ≫
        (ambientIso R κ n J B v hB hf hs L F T P).hom := by
  rw [← cancel_epi (T.mapIso (ActualCoordinateFlag.closedEquiv R κ n J B v).toUnder.op).hom]
  rw [← Category.assoc,comparison_square,Category.assoc,← Functor.map_comp,Iso.inv_hom_id,CategoryTheory.Functor.map_id,Category.comp_id,
    Iso.hom_inv_id_assoc]

#print axioms ambientIso
#print axioms flagIso
#print axioms comparison_square
#print axioms comparison_transport
end Verification.LocalizedActualPrincipal
