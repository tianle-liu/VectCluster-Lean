/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalSourceSheafEvaluation
import Verification.SheafReducedProjection
import Verification.AffineSuspendedEvaluation

/-!
# Original Source Reduced Kernel

The reduced source of the actual adjacent boundary is the literal
pullback of the original coefficient section minus its constant value at
u=1. All suspension and intermediate coordinate comparisons cancel.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalSourceReducedKernel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasFiniteBiproducts Z]
variable [HasZeroObject Z] [HasShift Z ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive] [Pretriangulated Z]
variable (J : DerivedCategory A ⥤ Z) [J.Additive] [J.CommShift ℤ]
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
variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (p : ℕ) (t : ActualCellThom.Index κ n B (p+1)) (v : Selected n t.val)
local notation "Sel" => Selected n t.val
local notation "Rest" => Other n t.val
local notation "D" => matrix κ n t.val B
local notation "μ" => CoordinateFlag.Old (Selected n t.val) v
local notation "F" => AffineRelativeThom.theory R μ G
local notation "S" => ActualAdjacentTorusBoundary.shiftedTheory R F ⋙ L
local notation "I" => ActualGlobalBoundary.edgeIndex κ n B p t v
local notation "Old" => ActualTorusReducedRestriction.OldBase R Sel (Rest ⊕ κ) Rest D v
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest D)
local notation "hD" => matrix_zero_block κ n t.val B hpos hneg hsupport t.property.2
local notation "hsNew" => (ActualTransversePairSmooth.pair_smooth_AS R Sel (Rest ⊕ κ) Rest Sum.inl D hD
  (hf t.val t.property.2) (hs t.val t.property.2) v).1
local notation "hsOld" => ActualOldFiberSmooth.old_smooth R Sel (Rest ⊕ κ) Rest D v Sum.inl hD
  (hf t.val t.property.2) (hs t.val t.property.2)
local notation "torusOld" => OriginalLocalizedTorusContraction.oldIso L R κ n t.val B v G H
  hpos hneg hsupport t.property.2 (hf t.val t.property.2) (hs t.val t.property.2)
local notation "torusNew" => OriginalLocalizedTorusContraction.torusNormalIso L R κ n t.val B v G H
  hpos hneg hsupport t.property.2 (hf t.val t.property.2) (hs t.val t.property.2)

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)

local notation "OldT" => ActualTorusFace.OldTorus R Sel (Rest ⊕ κ) Rest D v
local notation "OpenT" => ActualTransverseLocalization.OpenSource R Sel (Rest ⊕ κ) Rest Sum.inl D v
local notation "hTorus" => ActualOldTorusSmooth.old_smooth R Sel (Rest ⊕ κ) Rest Sum.inl D hD v
  (hf t.val t.property.2) (hs t.val t.property.2)
local notation "qmap" => (ActualTorusFace.oldZeroSection R Sel (Rest ⊕ κ) Rest Sum.inl D hD v).toUnder.op

include H in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive]
  [Pretriangulated Z] [L.IsTriangulated] [Preadditive Z] [L.Additive] in
theorem shifted_transport : (torusOld).hom ≫
    OriginalStrictContractionBlocks.sourceTransport L G E R κ n B P hpos hneg hsupport hf hs p t v =
    (((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app
      ((F).obj (op (CommRingCat.mkUnder (CommRingCat.of R) OldT)))).hom ≫
    (OriginalSourceSheafEvaluation.sourceAction L G R κ n B hpos hneg hsupport p t v)⟦(1 : ℤ)⟧' := by
  letI := OriginalLocalizedTorusContraction.old_projection L R κ n t.val B v G H
    hpos hneg hsupport t.property.2 (hf t.val t.property.2) (hs t.val t.property.2)
  have ho : (torusOld).hom = (DerivedCategory.Q ⋙ L).map (((F).map qmap)⟦(1 : ℤ)⟧') :=
    ActualTorusFace.oldIso_hom R Sel (Rest ⊕ κ) Rest Sum.inl D hD v S
  rw [ho,OriginalSourceTransportCancellation.transport_eq L G E R κ n B P hpos hneg hsupport hf hs p t v]
  have hn := ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.naturality ((F).map qmap)
  change (DerivedCategory.Q ⋙ L).map (((F).map qmap)⟦(1 : ℤ)⟧') ≫
    (((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app ((F).obj
      (op (CommRingCat.mkUnder (CommRingCat.of R) OpenT)))).hom =
    (((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app ((F).obj
      (op (CommRingCat.mkUnder (CommRingCat.of R) OldT)))).hom ≫
      ((DerivedCategory.Q ⋙ L).map ((F).map qmap))⟦(1 : ℤ)⟧' at hn
  simp only [Iso.app_hom] at hn
  rw [← Category.assoc,hn,Category.assoc,← CategoryTheory.Functor.map_comp]
  rfl

variable (j : ℤ)
local notation "Coef" => J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((p+1 : ℕ) : ℤ)) (M j)))
local notation "Test" => L.obj (ActualCellThom.localThom G R κ n B p I) ⟶
  J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(p : ℤ)) (M j)))

include hV in
omit [J.Additive] [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z]
  [L.Additive] [L.IsTriangulated] in
theorem shifted_evaluation (a : Test) :
    AffineShiftedThomSections.shiftedEvaluate J L G R OldT μ p
      (OriginalGradedContractionBlocks.old_card κ n B p t v) site M N V hTorus j
      ((torusOld).hom ≫ OriginalStrictContractionBlocks.sourceTransport L G E R κ n B P
        hpos hneg hsupport hf hs p t v ≫ StrictPositiveCoefficientTests.suspendTest J p (M j) _ a) =
    (N (j-p)).val.map (Spec.map (CommRingCat.ofHom
      (OriginalSourceCoefficientCoordinates.torusMap R κ n t.val B v hD).toRingHom)).op
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V p j I a) := by
  rw [← Category.assoc,shifted_transport L G E R κ n B P hpos hneg hsupport hf hs H p t v,Category.assoc]
  rw [AffineSuspendedEvaluation.evaluate_precompose]
  exact OriginalSourceSheafEvaluation.source_evaluation J L G R κ n B hpos hneg hsupport hf hs p t v site M N V hV j a

include hV in
omit [J.Additive] [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [L.IsTriangulated] in
theorem oldKernel_value (a : Test) :
    (OriginalGradedContractionBlocks.oldKernel J L G E R κ n B P hpos hneg hsupport hf hs H p t v
      site M N V hV j (StrictPositiveCoefficientTests.suspendTest J p (M j) _ a)).val =
    let z := (N (j-p)).val.map (Spec.map (CommRingCat.ofHom
      (OriginalSourceCoefficientCoordinates.torusMap R κ n t.val B v hD).toRingHom)).op
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V p j I a)
    z - SheafReducedProjection.coefficientPullback R Old site N (j-p)
      (AffineSheafContraction.sheafAtOne R Old site N (j-p) z) := by
  letI := hsOld
  rw [OriginalGradedContractionBlocks.oldKernel]
  change (AffineSheafContraction.contractionEquiv J L G R Old μ p
    (OriginalGradedContractionBlocks.old_card κ n B p t v) site M N V hV j
    (LocalizedSplitHomContraction.contraction (LaurentBasepoint.projection R Old F) L (1 : ℤ) Coef
      ((torusOld).hom ≫ OriginalStrictContractionBlocks.sourceTransport L G E R κ n B P
        hpos hneg hsupport hf hs p t v ≫ StrictPositiveCoefficientTests.suspendTest J p (M j) _ a))).val = _
  rw [SheafReducedProjection.contraction_value,shifted_evaluation J L G E R κ n B P
    hpos hneg hsupport hf hs H p t v site M N V hV j]

#print axioms shifted_transport
#print axioms shifted_evaluation
#print axioms oldKernel_value
end Verification.OriginalSourceReducedKernel
