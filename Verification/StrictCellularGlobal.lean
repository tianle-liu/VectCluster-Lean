/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictLocalizedCells
import Verification.StrictCellularTower
import Verification.PrimeIndependentHeight

/-!
# Strict Cellular Global

The actual original exchange space has a strict cellular model with
support bounded by its independence height. This is the retained attaching
cone tower of the actual open filtration, not an arbitrary bounded model.
The support bounds are derived from literal single-degree strict cells.
-/
noncomputable section
namespace Verification.StrictCellularGlobal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable [Nontrivial R] (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)

variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme, IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

def height : ℕ := PrimeIndependentHeight.height (Fin n) (Independent (laterWeights κ n B))

def emptyStage : IsZero (L.obj (DerivedCategory.Q.obj
    ((PrimeSchemeFiltration.filteredChains (Global R κ n B)
      (fun i => initial R κ n B (Sum.inl i)) G).obj 0))) := by
  have hz : IsEmpty ((PrimeSchemeFiltration.stages (Global R κ n B)
      (fun i => initial R κ n B (Sum.inl i))).obj 0) := by
    change IsEmpty (PrimeSchemeFiltration.stageOpen (Global R κ n B) _ 0)
    rw [show PrimeSchemeFiltration.stageOpen (Global R κ n B)
      (fun i => initial R κ n B (Sum.inl i)) 0 = ⊥ from PrimeCoordinateFiltration.stage_zero _]
    exact ⟨fun p => p.2⟩
  exact empty _ hz

def stage (p : ℕ) := StrictCellularTower.tower J L H
  (PrimeSchemeFiltration.filteredChains (Global R κ n B) (fun i => initial R κ n B (Sum.inl i)) G)
  (StrictLocalizedCells.cell J L G R T κ n B hpos hneg hsupport hf hs E P)
  (emptyStage L G R κ n B empty) p

def globalModel : Model J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R κ n B)))))) :=
  ofIso J (L.mapIso (DerivedCategory.Q.mapIso (G.mapIso
    (PrimeIndependentHeight.exhaustiveIso (Fin n) (Independent (laterWeights κ n B))
      (Global R κ n B) (fun i => initial R κ n B (Sum.inl i))
      (PrimeCoordinateFiltration.actual_zeroSet_independent R κ n B hpos hneg hsupport))))).symm
    (stage J L G R T κ n B hpos hneg hsupport hf hs E P H empty (height κ n B+1)).model

theorem support_lower : (globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty).complex.IsStrictlyGE
    (-(height κ n B : ℤ)) := by
  have h := (stage J L G R T κ n B hpos hneg hsupport hf hs E P H empty (height κ n B+1)).lower
  convert h using 1; push_cast; omega

theorem support_upper : (globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty).complex.IsStrictlyLE 0 :=
  (stage J L G R T κ n B hpos hneg hsupport hf hs E P H empty (height κ n B+1)).upper

#print axioms height
#print axioms emptyStage
#print axioms stage
#print axioms globalModel
#print axioms support_lower
#print axioms support_upper
end Verification.StrictCellularGlobal
