/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeCoordinateFlagBoundary
import Verification.IndependentOpenCoordinates

/-!
# Actual Global Boundary

Original exchange-space boundary blocks. Canonical global excision
and the fixed local pair comparisons give the coordinate-flag boundary
inside the J-chart; all nonincident blocks vanish. Acyclicity is used only
for the already proved independence of prime zero sets.
-/
noncomputable section
namespace Verification.ActualGlobalBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.PrimeLayerCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (r : ℕ) (J : Index (Independent (laterWeights κ n B)) (r+1))
local notation "A" => Global R κ n B
local notation "x" => fun i : Fin n => initial R κ n B (Sum.inl i)
local notation "Allowed" => Independent (laterWeights κ n B)
local notation "hall" => PrimeCoordinateFiltration.actual_zeroSet_independent R κ n B hpos hneg hsupport

omit [Fintype κ] in
theorem erase_allowed (v : J.val) : Allowed (J.val.erase v.val) := by
  intro i hi j hj
  exact J.property.2 i (Finset.mem_erase.mp hi).2 j (Finset.mem_erase.mp hj).2

def edgeIndex (v : J.val) : Index Allowed r :=
  PrimeAdjacentAssembly.edgeIndex (Fin n) Allowed J.val r J.property.1
    (erase_allowed κ n B r J) v

def block (I : Index Allowed r) :=
  PrimeGlobalBoundary.block A (Fin n) x Allowed G E hall r J I

theorem block_eq (I : Index Allowed r) : block R κ n B G E hpos hneg hsupport r J I =
    biproduct.ι (PrimeLayerExcision.localRelative A (Fin n) x Allowed G (r+1)) J ≫
      (PrimeLayerExcision.actualRelativeIso G E R κ n B hpos hneg hsupport (r+1)).hom ≫
      PrimeGlobalBoundary.globalBoundary A (Fin n) x G r ≫
      ((PrimeLayerExcision.actualRelativeIso G E R κ n B hpos hneg hsupport r).inv ≫
        biproduct.π (PrimeLayerExcision.localRelative A (Fin n) x Allowed G r) I)⟦(1 : ℤ)⟧' := by
  dsimp only [block,PrimeGlobalBoundary.block]
  rw [PrimeGlobalBoundary.inclusion_eq A (Fin n) x Allowed G E hall r J]
  simp only [Category.assoc,PrimeLayerExcision.actualRelativeIso]

theorem nonincident_zero (I : Index Allowed r) (hI : ¬ I.val ⊆ J.val) :
    block R κ n B G E hpos hneg hsupport r J I = 0 :=
  PrimeGlobalBoundary.block_zero A (Fin n) x Allowed G E hall r J
    (erase_allowed κ n B r J) I hI

def targetIso (v : Selected n J.val) :
    CoordinateFlag.oldRelative (BasicOpen R κ n J.val B) (Selected n J.val)
      (selectedCoordinate R κ n J.val B) v G ≅
    PrimeLayerExcision.localRelative A (Fin n) x Allowed G r (edgeIndex κ n B r J v) :=
  PrimeCoordinateFlagBoundary.targetIso A (Fin n) x Allowed G E r J v (erase_allowed κ n B r J)

theorem adjacent_boundary (v : Selected n J.val) :
    (PrimeLocalCone.layerIso A (Fin n) x G Allowed (r+1) J).hom ≫
      block R κ n B G E hpos hneg hsupport r J (edgeIndex κ n B r J v) =
    CoordinateFlag.boundary (BasicOpen R κ n J.val B) (Selected n J.val)
      (selectedCoordinate R κ n J.val B) v G ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (mappingCone (CoordinateFlag.firstArrow (BasicOpen R κ n J.val B) (Selected n J.val)
          (selectedCoordinate R κ n J.val B) v G)) ≫
        (targetIso R κ n B G E r J v).hom⟦(1 : ℤ)⟧' :=
  PrimeCoordinateFlagBoundary.block_boundary A (Fin n) x Allowed G E hall r J v (erase_allowed κ n B r J)

def targetCoordinateIso (v : Selected n J.val) :
    CoordinateFlag.oldRelative (BasicOpen R κ n J.val B) (Selected n J.val)
      (selectedCoordinate R κ n J.val B) v G ≅
    CoordinatePurityInput.relative (BasicOpen R κ n (J.val.erase v.val) B)
      (Selected n (J.val.erase v.val)) (selectedCoordinate R κ n (J.val.erase v.val) B) G :=
  targetIso R κ n B G E r J v ≪≫
    (PrimeLocalCone.layerIso A (Fin n) x G Allowed r (edgeIndex κ n B r J v)).symm

theorem adjacent_coordinate_boundary (v : Selected n J.val) :
    (PrimeLocalCone.layerIso A (Fin n) x G Allowed (r+1) J).hom ≫
      block R κ n B G E hpos hneg hsupport r J (edgeIndex κ n B r J v) ≫
        (PrimeLocalCone.layerIso A (Fin n) x G Allowed r (edgeIndex κ n B r J v)).inv⟦(1 : ℤ)⟧' =
    CoordinateFlag.boundary (BasicOpen R κ n J.val B) (Selected n J.val)
      (selectedCoordinate R κ n J.val B) v G ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (mappingCone (CoordinateFlag.firstArrow (BasicOpen R κ n J.val B) (Selected n J.val)
          (selectedCoordinate R κ n J.val B) v G)) ≫
        (targetCoordinateIso R κ n B G E r J v).hom⟦(1 : ℤ)⟧' := by
  rw [reassoc_of% (adjacent_boundary R κ n B G E hpos hneg hsupport r J v)]
  simp only [targetCoordinateIso,Iso.trans_hom,Iso.symm_hom,
    CategoryTheory.Functor.map_comp,Category.assoc]

#print axioms erase_allowed
#print axioms edgeIndex
#print axioms block
#print axioms block_eq
#print axioms nonincident_zero
#print axioms targetIso
#print axioms adjacent_boundary
#print axioms targetCoordinateIso
#print axioms adjacent_coordinate_boundary
end Verification.ActualGlobalBoundary
