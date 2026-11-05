/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedIndexedPurity
import Verification.CoordinateEquivInverse
import Verification.CanonicalAdjacentTarget
import Verification.LocalizedActualFlag

/-!
# Actual Indexed Purity

The fixed purity comparison in the adjacent I-chart is compatible with
the localized old-coordinate frame in the J-chart. The index bijection,
ring equivalence, original coordinate identities and all AS frame
hypotheses are supplied internally; the input is ordinary indexed purity
naturality, without a cellular differential assertion.
-/
noncomputable section
namespace Verification.ActualIndexedPurity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.PrimeLayerCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D]
variable (L : DerivedCategory C ⥤ D)
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (N : LocalizedIndexedPurity.Standard L R G P)
variable (r : ℕ) (J : Index (Independent (laterWeights κ n B)) (r+1)) (v : Selected n J.val)
local notation "A" => Global R κ n B
local notation "W" => BasicOpen R κ n J.val B
local notation "S" => Selected n J.val
local notation "y" => selectedCoordinate R κ n J.val B
local notation "Wv" => CoordinateLocalizationPair.OpenRing W S y v
local notation "q" => CoordinateLocalizationPair.coordinate W S y v
local notation "Wi" => BasicOpen R κ n (J.val.erase v.val) B
local notation "I" => ActualGlobalBoundary.edgeIndex κ n B r J v
local notation "z" => selectedCoordinate R κ n (J.val.erase v.val) B
local notation "ν" => AdjacentCoordinatePair.indexEquiv n J.val v
local notation "e" => AdjacentCoordinatePair.equiv n J.val v R κ B

omit [Nontrivial R] in
theorem inverse_coordinate (i : CoordinateFlag.Old S v) : (e).symm (z (ν i)) = q i :=
  CoordinateEquivInverse.inverse_coordinate q (z ∘ ν) (e).toRingEquiv
    (AdjacentCoordinatePair.equiv_coordinate n J.val v R κ B) i

omit [Nontrivial R] in
def normalTransport : CoordinatePurityInput.normalThom Wv (CoordinateFlag.Old S v) q G ⟶
    CoordinatePurityInput.normalThom Wi (Selected n (J.val.erase v.val)) z G :=
  ReindexedCoordinateMap.normalMap z q ν (e).symm.toRingHom (inverse_coordinate R κ n B r J v) G

omit [Nontrivial R] in
theorem pairMap_eq :
    ReindexedCoordinateMap.relativeMap z q ν (e).symm.toRingHom (inverse_coordinate R κ n B r J v) G =
      (AdjacentCoordinatePair.relativeIso n J.val v R κ B G).hom := by
  dsimp only [ReindexedCoordinateMap.relativeMap,AdjacentCoordinatePair.relativeIso,
    Iso.trans_hom,Iso.symm_hom]
  rfl

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ K, Independent (laterWeights κ n B) K →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B K))
variable (hs : ∀ K, Independent (laterWeights κ n B) K →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B K)))

def sourceFrame := LocalizedOldCoordinateFrame.frame R κ n J.val B v hpos hneg hsupport
  J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)

def targetFrame := IndependentCoordinatePurity.frame R κ n (I).val B hpos hneg hsupport
  (I).property.2 (hf (I).val (I).property.2) (hs (I).val (I).property.2)

include N in
theorem adjacent_purity :
    L.map (AdjacentCoordinatePair.relativeIso n J.val v R κ B G).hom ≫
      (P.comparison Wi (Selected n (J.val.erase v.val)) z
        (targetFrame R κ n B r J v hpos hneg hsupport hf hs)).hom =
    (P.comparison Wv (CoordinateFlag.Old S v) q
      (sourceFrame R κ n B r J v hpos hneg hsupport hf hs)).hom ≫
        L.map (normalTransport R κ n B G r J v) := by
  let f : Wi →ₐ[R] Wv := (e).symm.toAlgHom
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    change IsOpenImmersion (CoordinatePairEquiv.schemeIso (e).toRingEquiv).hom
    infer_instance
  have h := N.open_naturality Wi Wv (Selected n (J.val.erase v.val)) (CoordinateFlag.Old S v)
    z q ν f (inverse_coordinate R κ n B r J v)
    (targetFrame R κ n B r J v hpos hneg hsupport hf hs)
    (sourceFrame R κ n B r J v hpos hneg hsupport hf hs)
  simpa only [pairMap_eq,normalTransport] using h

include N in
theorem fixed_target_purity :
    L.map (ActualGlobalBoundary.targetCoordinateIso R κ n B G E r J v).hom ≫
      (P.comparison Wi (Selected n (J.val.erase v.val)) z
        (targetFrame R κ n B r J v hpos hneg hsupport hf hs)).hom =
    (LocalizedFlagPairs.oldComparison L R W S y v G E P
      (sourceFrame R κ n B r J v hpos hneg hsupport hf hs)).hom ≫
        L.map (normalTransport R κ n B G r J v) := by
  rw [← cancel_epi (L.map (CoordinateLocalizationPair.oldRelativeIso W S y v G E).hom)]
  simp only [LocalizedFlagPairs.oldComparison,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_inv,← Category.assoc,← Functor.map_comp,Iso.hom_inv_id,
    CategoryTheory.Functor.map_id,Category.id_comp]
  rw [CanonicalAdjacentTarget.target_compatibility]
  exact adjacent_purity L R κ n B G P N r J v hpos hneg hsupport hf hs

#print axioms inverse_coordinate
#print axioms normalTransport
#print axioms pairMap_eq
#print axioms sourceFrame
#print axioms targetFrame
#print axioms adjacent_purity
#print axioms fixed_target_purity
end Verification.ActualIndexedPurity
