/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedCoordinatePurity
import Verification.ActualCellThom
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Localized Actual Cell Thom

Actual cellular layers identified after the ambient localization L.
AS proves every frame and the actual open excision remains canonical.
Homotopy purity is assumed only in the localized ambient category, never
as an ordinary derived quasi-isomorphism of raw Nisnevich chains.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.LocalizedActualCellThom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I → Function.Injective (selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I)))

def localIso (r : ℕ) (i : ActualCellThom.Index κ n B r) :
    L.obj (PrimeLayerExcision.localRelative (Global R κ n B) (Fin n)
      (fun j => initial R κ n B (Sum.inl j)) (Independent (laterWeights κ n B)) G r i) ≅
        L.obj (ActualCellThom.localThom G R κ n B r i) :=
  L.mapIso (PrimeLocalCone.layerIso (Global R κ n B) (Fin n)
    (fun j => initial R κ n B (Sum.inl j)) G (Independent (laterWeights κ n B)) r i).symm ≪≫
      P.comparison (BasicOpen R κ n i.val B) (Selected n i.val) (selectedCoordinate R κ n i.val B)
        (IndependentCoordinatePurity.frame R κ n i.val B hpos hneg hsupport i.property.2
          (hf i.val i.property.2) (hs i.val i.property.2))

def relativeIso (r : ℕ) :
    L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative (PrimeSchemeFiltration.filteredChains
      (Global R κ n B) (fun j => initial R κ n B (Sum.inl j)) G) r)) ≅
        ⨁ fun i : ActualCellThom.Index κ n B r => L.obj (ActualCellThom.localThom G R κ n B r i) :=
  L.mapIso (PrimeLayerExcision.actualRelativeIso G E R κ n B hpos hneg hsupport r).symm ≪≫
    L.mapBiproduct (PrimeLayerExcision.localRelative (Global R κ n B) (Fin n)
      (fun j => initial R κ n B (Sum.inl j)) (Independent (laterWeights κ n B)) G r) ≪≫
      biproduct.mapIso (localIso L G R κ n B P hpos hneg hsupport hf hs r)

#print axioms localIso
#print axioms relativeIso
end Verification.LocalizedActualCellThom
