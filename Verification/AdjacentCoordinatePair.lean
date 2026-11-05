/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AdjacentChartLocalization
import Verification.IndependentOpenCoordinates
import Verification.CoordinateLocalizationPair
import Verification.CoordinatePairReindex

/-!
# Adjacent Coordinate Pair

The actual old-coordinate principal-open pair in a J-chart is the
coordinate pair in the (J minus v)-chart. Both the index equivalence and
the ring equivalence preserve each original mutable coordinate.
-/
noncomputable section
namespace Verification.AdjacentCoordinatePair
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.IndependentOpenCoordinates
variable (n : ℕ) (J : Finset (Fin n)) (v : Selected n J)

def indexEquiv : CoordinateFlag.Old (Selected n J) v ≃ Selected n (J.erase v.val) where
  toFun i := ⟨i.val.val,Finset.mem_erase.mpr ⟨fun h => i.property (Subtype.ext h),i.val.property⟩⟩
  invFun i := ⟨⟨i.val,(Finset.mem_erase.mp i.property).2⟩,fun h =>
    (Finset.mem_erase.mp i.property).1 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem indexEquiv_coordinate (i : CoordinateFlag.Old (Selected n J) v) :
    (indexEquiv n J v i).val = i.val.val := rfl

variable (R κ : Type) [CommRing R] [Fintype κ]
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
local notation "A" => Global R κ n B
local notation "W" => BasicOpen R κ n J B
local notation "S" => Selected n J
local notation "x" => selectedCoordinate R κ n J B
local notation "Wv" => CoordinateLocalizationPair.OpenRing W S x v
local notation "y" => CoordinateLocalizationPair.coordinate W S x v
local notation "Wi" => BasicOpen R κ n (J.erase v.val) B
local notation "z" => selectedCoordinate R κ n (J.erase v.val) B

def equiv : Wv ≃ₐ[R] Wi :=
  (AdjacentChartLocalization.equiv (fun i => initial R κ n B (Sum.inl i)) J v).restrictScalars R

theorem equiv_original (a : A) : equiv n J v R κ B (algebraMap A Wv a) = algebraMap A Wi a :=
  AdjacentChartLocalization.equiv_coordinate (fun i => initial R κ n B (Sum.inl i)) J v a

theorem equiv_coordinate (i : CoordinateFlag.Old S v) :
    equiv n J v R κ B (y i) = z (indexEquiv n J v i) := by
  change equiv n J v R κ B (algebraMap W Wv
    (algebraMap A W (initial R κ n B (Sum.inl i.val.val)))) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact equiv_original n J v R κ B _

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def relativeIso : CoordinatePurityInput.relative Wv (CoordinateFlag.Old S v) y G ≅
    CoordinatePurityInput.relative Wi (Selected n (J.erase v.val)) z G :=
  CoordinatePairEquiv.relativeIso y (z ∘ indexEquiv n J v)
    (equiv n J v R κ B).toRingEquiv (equiv_coordinate n J v R κ B) G ≪≫
      (CoordinatePairReindex.relativeIso Wi (Selected n (J.erase v.val))
        (CoordinateFlag.Old S v) z (indexEquiv n J v) G).symm

#print axioms indexEquiv
#print axioms indexEquiv_coordinate
#print axioms equiv
#print axioms equiv_original
#print axioms equiv_coordinate
#print axioms relativeIso
end Verification.AdjacentCoordinatePair
