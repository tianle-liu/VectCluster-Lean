/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictSingleModel
import Verification.StrictLocalizedAcyclic

/-!
# Strict Localized Cells

Actual AS layers have single-degree projective strict models. Only
standard split torus--Thom objects carry an external strict representer;
all original strata, their finite sums and the localized purity transport
are constructed internally.
-/
noncomputable section
namespace Verification.StrictLocalizedCells
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.StrictSingleModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R]

structure TorusCells where
  cell : ∀ (ι τ κ : Type) [Fintype ι] [Fintype τ] [Fintype κ],
    Cell J (-(Fintype.card ι : ℤ)) (L.obj (TorusThomInput.thom R ι τ κ G))

variable (T : TorusCells J L G R)
variable [Nontrivial R] (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

def localCell (r : ℕ) (i : ActualCellThom.Index κ n B r) :
    Cell J (-(r : ℤ)) (L.obj (ActualCellThom.localThom G R κ n B r i)) :=
  redegree (ofIso (T.cell (Selected n i.val) (Selected n i.val)
    (Fin (IndependentStratumTorus.torusRank κ n i.val B)))
    (L.mapIso (CompatibleTorusThom.explicitIso G R κ n B hpos hneg hsupport hf hs r i)))
    (by simp only [Selected,Fintype.card_coe,i.property.1])

variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)

def cell (r : ℕ) : Cell J (-(r : ℤ))
    (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative
      (PrimeSchemeFiltration.filteredChains (Global R κ n B)
        (fun i => initial R κ n B (Sum.inl i)) G) r))) :=
  ofIso (sum (fun i => L.obj (ActualCellThom.localThom G R κ n B r i))
    (localCell J L G R T κ n B hpos hneg hsupport hf hs r))
    (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs r)

#print axioms TorusCells
#print axioms localCell
#print axioms cell
end Verification.StrictLocalizedCells
