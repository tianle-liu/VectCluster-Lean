/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualCoordinateFlag
import Verification.ActualTransverseCone
import Verification.RelativeProductFunctor
import Verification.ConeDerivedComparison

/-!
# Actual Flag Arrow

The actual coordinate flag's principal-open arrow is isomorphic to
the original transverse exchange arrow. This isomorphism comes from the
proved algebra equivalences and preserves the positive cone boundary.
-/
noncomputable section
namespace Verification.ActualFlagArrow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
local notation "A" => BasicOpen R κ n J B
local notation "Sel" => Selected n J
local notation "K" => Other n J ⊕ κ
local notation "Rest" => Other n J
local notation "D" => matrix κ n J B
local notation "x" => selectedCoordinate R κ n J B
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)

def oldArrow := F.map (IsScalarTower.toAlgHom R (CoordinateFlag.ClosedOld A Sel x v)
  (CoordinateFlag.OpenOld A Sel x v)).toUnder.op

def arrowIso : Arrow.mk (ActualTransverseCone.ambientOpen R Sel K Rest Sum.inl D v F) ≅
    Arrow.mk (oldArrow R κ n J B v F) :=
  Arrow.isoMk (F.mapIso (ActualCoordinateFlag.openEquiv R κ n J B v).toUnder.op)
    (F.mapIso (ActualCoordinateFlag.intermediateEquiv R κ n J B v).toUnder.op) (by
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp]
      apply congrArg F.map
      exact congrArg (fun f : CoordinateFlag.ClosedOld A Sel x v →ₐ[R]
        ActualTransverseLocalization.OpenSource R Sel K Rest Sum.inl D v => (AlgHom.toUnder (R := CommRingCat.of R) f).op)
          (ActualCoordinateFlag.open_square R κ n J B v))

def complexIso : mappingCone (oldArrow R κ n J B v F) ≅
    mappingCone (ActualTransverseCone.ambientOpen R Sel K Rest Sum.inl D v F) :=
  (RelativeProductFunctor.coneFunctor.mapIso (arrowIso R κ n J B v F)).symm

universe w
variable [HasDerivedCategory.{w} C]

def coneIso : DerivedCategory.Q.obj (mappingCone (oldArrow R κ n J B v F)) ≅
    DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.ambientOpen R Sel K Rest Sum.inl D v F)) :=
  DerivedCategory.Q.mapIso (complexIso R κ n J B v F)

theorem positive_boundary : (coneIso R κ n J B v F).hom ≫
    TransverseDerivedBoundary.boundary (ActualTransverseCone.ambientOpen R Sel K Rest Sum.inl D v F) =
      TransverseDerivedBoundary.boundary (oldArrow R κ n J B v F) ≫
        DerivedCategory.Q.map (((F.mapIso (ActualCoordinateFlag.openEquiv R κ n J B v).toUnder.op).inv)⟦(1 : ℤ)⟧') :=
  TransverseDerivedBoundary.boundary_naturality _ _ _ _ (arrowIso R κ n J B v F).inv.w.symm

#print axioms oldArrow
#print axioms arrowIso
#print axioms complexIso
#print axioms coneIso
#print axioms positive_boundary
end Verification.ActualFlagArrow
