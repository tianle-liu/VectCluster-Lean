/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictNormalizedDifferential
import Verification.OriginalLocalizedTorusContraction

/-!
# Original Strict Contraction Blocks

Every adjacent block of the actual strict differential is computed by
the actual Laurent contraction and fiber restriction. The source transport
is constructed from the original flag, open-coordinate and adjacent-frame
maps; no matrix or differential compatibility is assumed.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalStrictContractionBlocks
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasFiniteBiproducts Z]
variable [HasZeroObject Z] [HasShift Z ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive] [Pretriangulated Z]
variable (L : DerivedCategory C ⥤ Z) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
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
variable (N : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (p : ℕ) (J : ActualCellThom.Index κ n B (p+1)) (v : Selected n J.val)
local notation "W" => BasicOpen R κ n J.val B
local notation "Sel" => Selected n J.val
local notation "x" => selectedCoordinate R κ n J.val B
local notation "Rest" => Other n J.val
local notation "D" => matrix κ n J.val B
local notation "F" => AffineRelativeThom.theory R (CoordinateFlag.Old (Selected n J.val) v) G
local notation "S" => ActualAdjacentTorusBoundary.shiftedTheory R F ⋙ L
local notation "I" => ActualGlobalBoundary.edgeIndex κ n B p J v
local notation "O" => ActualTransverseLocalization.OpenSource R Sel (Rest ⊕ κ) Rest Sum.inl D v
local notation "OldT" => ActualTorusFace.OldTorus R Sel (Rest ⊕ κ) Rest D v
local notation "oldFrame" => ActualIndexedPurity.sourceFrame R κ n B p J v hpos hneg hsupport hf hs
local notation "o" => LocalizedActualFlag.oldIso L R κ n J.val B v G E P hpos hneg hsupport
  J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "a" => (LocalizedFlagPairs.oldComparison L R W Sel x v G E P oldFrame).hom ≫
  L.map (ActualIndexedPurity.normalTransport R κ n B G p J v)
local notation "full" => P.comparison W Sel x (IndependentCoordinatePurity.frame R κ n J.val B
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2))
local notation "torusOld" => OriginalLocalizedTorusContraction.oldIso L R κ n J.val B v G H
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "torusNew" => OriginalLocalizedTorusContraction.torusNormalIso L R κ n J.val B v G H
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "thomNew" => OriginalLocalizedTorusContraction.fiberThomIso L R κ n J.val B v G E P K H
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "adj" => LocalizedActualTransverse.adjacentBoundary L R κ n J.val B v G E P K
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "normal" => LocalizedActualTransverse.normalIso L R κ n J.val B v G

def openIso : (DerivedCategory.Q ⋙ L).obj
    ((CochainComplex.mappingCone (CoordinateFlag.firstArrow W Sel x v G))⟦(1 : ℤ)⟧) ≅
    (S).obj (op (CommRingCat.mkUnder (CommRingCat.of R) O)) :=
  LocalizedFlagCoherence.shiftedIso L o ≪≫
    (DerivedCategory.Q ⋙ L).mapIso ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).mapIso
      ((F).mapIso (ActualCoordinateFlag.openEquiv R κ n J.val B v).toUnder.op).symm)

def sourceTransport : (S).obj (op (CommRingCat.mkUnder (CommRingCat.of R) O)) ⟶
    (L.obj (ActualCellThom.localThom G R κ n B p I))⟦(1 : ℤ)⟧ :=
  (openIso L G E R κ n B P hpos hneg hsupport hf hs p J v).inv ≫
    ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app
      (CochainComplex.mappingCone (CoordinateFlag.firstArrow W Sel x v G)) ≫ (a)⟦(1 : ℤ)⟧'

omit [HasFiniteBiproducts Z] [HasZeroObject Z] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive]
  [Pretriangulated Z] [L.IsTriangulated] in
theorem normalized_transverse :
    FixedNormalizedBoundary.normalizedBoundary L R κ n B G E P p J v hpos hneg hsupport hf hs K =
    (full).hom ≫ (normal).hom ≫ adj ≫
      sourceTransport L G E R κ n B P hpos hneg hsupport hf hs p J v := by
  have hb := LocalizedActualTransverse.positive_boundary L R κ n J.val B v G E P K
    hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
  have hh := congrArg (fun f => f ≫
    sourceTransport L G E R κ n B P hpos hneg hsupport hf hs p J v) hb
  change ((full).hom ≫ (normal).hom ≫ adj) ≫ _ =
    (L.map (CoordinateFlag.boundary W Sel x v G) ≫
      (openIso L G E R κ n B P hpos hneg hsupport hf hs p J v).hom) ≫ _ at hh
  simp only [sourceTransport, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [FixedNormalizedBoundary.flag_normalized L R κ n B G E P p J v hpos hneg hsupport hf hs K] at hh
  exact hh.symm

include N in
omit [HasZeroObject Z] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive]
  [Pretriangulated Z] [L.IsTriangulated] in
theorem positive_transverse :
    OriginalStrictBoundaryGeometry.positiveBlock L G E R κ n B P hpos hneg hsupport hf hs p J I =
    (normal).hom ≫ adj ≫ sourceTransport L G E R κ n B P hpos hneg hsupport hf hs p J v := by
  rw [OriginalStrictNormalizedDifferential.adjacent_normalized L G E R κ n B P hpos hneg hsupport hf hs N K,
    normalized_transverse L G E R κ n B P hpos hneg hsupport hf hs K p J v]
  simp only [Iso.inv_hom_id_assoc]

variable (M : Z)
include N in
theorem positive_on_sections
    (b : (L.obj (ActualCellThom.localThom G R κ n B p I))⟦(1 : ℤ)⟧ ⟶ M) :
    OriginalStrictBoundaryGeometry.positiveBlock L G E R κ n B P hpos hneg hsupport hf hs p J I ≫ b =
    (torusNew).hom ≫ (thomNew).hom ≫
      L.map (DerivedCategory.Q.map ((ActualTorusReducedRestriction.reducedRestriction
        R Sel (Rest ⊕ κ) Rest D v F)⟦(1 : ℤ)⟧')) ≫
      LocalizedTorusContraction.oldContraction R Sel (Rest ⊕ κ) Rest D v L F M
        ((torusOld).hom ≫ sourceTransport L G E R κ n B P hpos hneg hsupport hf hs p J v ≫ b) := by
  rw [positive_transverse L G E R κ n B P hpos hneg hsupport hf hs N K p J v]
  have hh := OriginalLocalizedTorusContraction.adjacent_on_sections L R κ n J.val B v G E P K H
    hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2) M
    ((torusOld).hom ≫ sourceTransport L G E R κ n B P hpos hneg hsupport hf hs p J v ≫ b)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh

def contractionBlock : L.obj (ActualCellThom.localThom G R κ n B (p+1) J) ⟶
    (L.obj (ActualCellThom.localThom G R κ n B p I))⟦(1 : ℤ)⟧ :=
  (torusNew).hom ≫ (thomNew).hom ≫
    L.map (DerivedCategory.Q.map ((ActualTorusReducedRestriction.reducedRestriction
      R Sel (Rest ⊕ κ) Rest D v F)⟦(1 : ℤ)⟧')) ≫
    LocalizedTorusContraction.oldContraction R Sel (Rest ⊕ κ) Rest D v L F
      ((L.obj (ActualCellThom.localThom G R κ n B p I))⟦(1 : ℤ)⟧)
      ((torusOld).hom ≫ sourceTransport L G E R κ n B P hpos hneg hsupport hf hs p J v)

include N in
theorem positive_eq_contraction :
    OriginalStrictBoundaryGeometry.positiveBlock L G E R κ n B P hpos hneg hsupport hf hs p J I =
    contractionBlock L G E R κ n B P hpos hneg hsupport hf hs K H p J v := by
  have h := positive_on_sections L G E R κ n B P hpos hneg hsupport hf hs N K H p J v
    ((L.obj (ActualCellThom.localThom G R κ n B p I))⟦(1 : ℤ)⟧) (𝟙 _)
  simpa only [contractionBlock, Category.comp_id] using h

#print axioms openIso
#print axioms sourceTransport
#print axioms normalized_transverse
#print axioms positive_transverse
#print axioms positive_on_sections
#print axioms contractionBlock
#print axioms positive_eq_contraction
end Verification.OriginalStrictContractionBlocks
