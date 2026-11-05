/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeLocalCone
import Verification.IndependentCoordinatePurity

/-!
# Actual Cell Thom

Termwise geometric purity for the original cellular filtration. Canonical
open excision, actual localization charts, and internally verified AS frames
identify every relative layer with the direct sum of the actual normal Thom
cones of its independent original strata.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.ActualCellThom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (P : CoordinatePurityInput.StandardPurity R G)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I → Function.Injective (selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I)))

abbrev Index (r : ℕ) := PrimeLayerCover.Index (Independent (laterWeights κ n B)) r

def localThom (r : ℕ) (i : Index κ n B r) : DerivedCategory C :=
  CoordinatePurityInput.normalThom (BasicOpen R κ n i.val B) (Selected n i.val)
    (selectedCoordinate R κ n i.val B) G

def localIso (r : ℕ) (i : Index κ n B r) :
    PrimeLayerExcision.localRelative (Global R κ n B) (Fin n)
      (fun j => initial R κ n B (Sum.inl j)) (Independent (laterWeights κ n B)) G r i ≅
        localThom G R κ n B r i :=
  (PrimeLocalCone.layerIso (Global R κ n B) (Fin n)
    (fun j => initial R κ n B (Sum.inl j)) G (Independent (laterWeights κ n B)) r i).symm ≪≫
      IndependentCoordinatePurity.comparison R κ n i.val B hpos hneg hsupport i.property.2
        (hf i.val i.property.2) (hs i.val i.property.2) G P

def relativeIso (r : ℕ) :
    DerivedCategory.Q.obj (FilteredConeComplex.relative (PrimeSchemeFiltration.filteredChains
      (Global R κ n B) (fun j => initial R κ n B (Sum.inl j)) G) r) ≅
        ⨁ fun i : Index κ n B r => localThom G R κ n B r i :=
  (PrimeLayerExcision.actualRelativeIso G E R κ n B hpos hneg hsupport r).symm ≪≫
    biproduct.mapIso (localIso G R κ n B P hpos hneg hsupport hf hs r)

#print axioms Index
#print axioms localThom
#print axioms localIso
#print axioms relativeIso
end Verification.ActualCellThom
