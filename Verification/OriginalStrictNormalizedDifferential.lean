/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictBoundaryGeometry
import Verification.FixedNormalizedBoundary

/-!
# Original Strict Normalized Differential

The adjacent block of the actual strict coefficient differential is
the fixed normalized principal-flag boundary, in the original normal frames.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalStrictNormalizedDifferential
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable [HasZeroObject D] [HasShift D ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor D q).Additive] [Pretriangulated D]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
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

local notation "A₀" => Global R κ n B
local notation "xs" => fun j : Fin n => initial R κ n B (Sum.inl j)
local notation "Allowed" => Independent (laterWeights κ n B)
local notation "Fil" => PrimeSchemeFiltration.filteredChains A₀ xs G

omit [HasZeroObject D] [∀ q : ℤ, (CategoryTheory.shiftFunctor D q).Additive]
  [Pretriangulated D] [L.IsTriangulated] in
theorem adjacent_normalized
    (N : LocalizedIndexedPurity.Standard L R G P)
    (K : LocalizedNormalizedFlag.Standard L R G E P)
    (p : ℕ) (j : ActualCellThom.Index κ n B (p+1)) (v : Selected n j.val) :
    OriginalStrictBoundaryGeometry.positiveBlock L G E R κ n B P hpos hneg hsupport hf hs p j
      (ActualGlobalBoundary.edgeIndex κ n B p j v) =
    (P.comparison (BasicOpen R κ n j.val B) (Selected n j.val)
      (selectedCoordinate R κ n j.val B)
      (IndependentCoordinatePurity.frame R κ n j.val B hpos hneg hsupport j.property.2
        (hf j.val j.property.2) (hs j.val j.property.2))).inv ≫
      FixedNormalizedBoundary.normalizedBoundary L R κ n B G E P p j v hpos hneg hsupport hf hs K := by
  apply (cancel_epi (P.comparison (BasicOpen R κ n j.val B) (Selected n j.val)
    (selectedCoordinate R κ n j.val B)
    (IndependentCoordinatePurity.frame R κ n j.val B hpos hneg hsupport j.property.2
      (hf j.val j.property.2) (hs j.val j.property.2))).hom).mp
  rw [OriginalStrictBoundaryGeometry.positiveBlock_eq]
  simp only [LocalizedActualCellThom.localIso,Iso.trans_inv,Iso.trans_hom,Iso.symm_inv,Iso.symm_hom,
    Functor.mapIso_inv,Functor.mapIso_hom,Category.assoc,Iso.hom_inv_id_assoc]
  exact FixedNormalizedBoundary.global_normalized L R κ n B G E P N p j v
    hpos hneg hsupport hf hs K

#print axioms adjacent_normalized
end Verification.OriginalStrictNormalizedDifferential
