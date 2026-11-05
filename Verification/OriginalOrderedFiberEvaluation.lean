/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalCanonicalFiberProjection
import Verification.OriginalLocalizedTorusContraction
import Verification.OrderedAffineFlagEvaluation
import Verification.AffineShiftedThomNaturality
import Verification.ActualSheafContractionRestriction
import Verification.OrientationBaseNaturality

/-!
# Original Ordered Fiber Evaluation

Compare increasing original-stratum coefficient sections with the
actual none-first transverse torus frame. The target projection is the
canonical partner-zero map, proved independent of the adjacent flag.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalOrderedFiberEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w₁ w₂
variable {A₀ C : Type*} [Category A₀] [Abelian A₀] [HasDerivedCategory.{w₁} A₀]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasZeroObject Z] [HasShift Z ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive] [Pretriangulated Z]
variable (J : DerivedCategory A₀ ⥤ Z) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ Z) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (I : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n I)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hI : Independent (laterWeights κ n B) I)
variable (hf : Function.Injective (selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I)))
local instance selectedOrder : LinearOrder (Selected n I) := ActualNormalizedFlag.selectedOrder n I
local notation "A" => BasicOpen R κ n I B
local notation "Sel" => Selected n I
local notation "Rest" => Other n I
local notation "D" => matrix κ n I B
local notation "x" => selectedCoordinate R κ n I B
local notation "All" => CoordinateFlag.ClosedAll A Sel x v
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest D)
local notation "F" => AffineRelativeThom.theory R (Option (CoordinateFlag.Old Sel v)) G
local notation "T" => AffineRelativeThom.theory R (Option (CoordinateFlag.Old Sel v)) G ⋙ DerivedCategory.Q ⋙ L
local notation "hD" => matrix_zero_block κ n I B hpos hneg hsupport hI
local notation "hframe" => IndependentCoordinatePurity.frame R κ n I B hpos hneg hsupport hI hf hs
local notation "hAll" => PrincipalFlagComparison.closed_smooth R A Sel x v hframe
local notation "hNew" => (ActualTransversePairSmooth.pair_smooth_AS R Sel (Rest ⊕ κ) Rest Sum.inl D hD hf hs v).1
local notation "hZero" => IndependentCoordinatePurity.closed_smooth R κ n I B hpos hneg hsupport hI hf hs
local notation "normal" => L.mapIso (FlagNormalCoordinates.thomIso R A Sel x v G)
local notation "torusNew" => OriginalLocalizedTorusContraction.torusNormalIso L R κ n I B v G H
  hpos hneg hsupport hI hf hs
local instance optionOrder : LinearOrder (Option (CoordinateFlag.Old Sel v)) :=
  inferInstanceAs (LinearOrder (WithBot (CoordinateFlag.Old Sel v)))

def closedProjection : All →ₐ[R] New :=
  (ActualTransverseLocalization.closedSlice R Sel (Rest ⊕ κ) Rest Sum.inl D hD v).comp
    (ActualCoordinateFlag.closedEquiv R κ n I B v).toAlgHom

omit [HasZeroObject Z] [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive]
  [Pretriangulated Z] [L.IsTriangulated] [Nontrivial R] [Preadditive Z]
  [HasShift Z ℤ] [L.Additive] [L.CommShift ℤ] in
theorem inverse_torusNormal : (torusNew).inv =
    (T).map (closedProjection R κ n I B v hpos hneg hsupport hI).toUnder.op ≫ (normal).inv := by
  letI := OriginalLocalizedTorusContraction.closed_projection L R κ n I B v G H
    hpos hneg hsupport hI hf hs
  simp only [OriginalLocalizedTorusContraction.torusNormalIso,
    OriginalLocalizedTorusContraction.closedIso, LocalizedActualTransverse.normalIso,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Category.assoc,
    LocalizedSlicePurity.closedIso_hom]
  unfold LocalizedSlicePurity.closedMap
  rw [← Functor.map_comp_assoc]
  rfl

variable (r : ℕ) (hr : Fintype.card (Selected n I) = r)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A₀) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (j : ℤ)
local notation "Coef" => J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))

include hV in
omit [J.Additive] [L.Additive] [J.CommShift ℤ] [L.CommShift ℤ] [HasZeroObject Z] [HasShift Z ℤ]
  [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive] [Pretriangulated Z] [L.IsTriangulated] in
theorem projection_evaluation
    (a : L.obj (CoordinatePurityInput.normalThom A Sel x G) ⟶ Coef) :
    ActualSheafContractionRestriction.pullback site (N (j-r))
      (OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI).toRingHom
      (OrderedThomSections.evaluate Sel r hr (GlobalNormalFrame.ZeroLayer R κ n I B)
        J L G R site M N V hZero j a) =
    ActualSheafContractionRestriction.pullback site (N (j-r))
      (closedProjection R κ n I B v hpos hneg hsupport hI).toRingHom
      ((O.orientation All (j-r) (-1) ^
        ((Finset.univ.erase v).filter (fun i : Sel => i < v)).card)
        (AffineShiftedThomSections.evaluate J L G R All (Option (CoordinateFlag.Old Sel v)) r
          ((OrderedOptionFlagNumbering.card_count Sel v).trans
            ((OrderedFlagNumbering.card_count Sel v).symm.trans hr)) site M N V hAll j
          ((normal).inv ≫ a))) := by
  have hc : r = OrderedFlagNormalCoordinates.count Sel v := hr.symm.trans (OrderedFlagNumbering.card_count Sel v)
  cases hc
  rw [OriginalCanonicalFiberProjection.projection_factorization R κ n I B v hpos hneg hsupport hI]
  change ActualSheafContractionRestriction.pullback site (N _)
    ((closedProjection R κ n I B v hpos hneg hsupport hI).toRingHom.comp
      (CoordinateFlagTotalQuotient.equiv R A Sel x v).symm.toRingHom) _ = _
  rw [ActualSheafContractionRestriction.pullback_comp]
  change ActualSheafContractionRestriction.pullback site (N _)
    (closedProjection R κ n I B v hpos hneg hsupport hI).toRingHom
    ((N _).val.map (Spec.map (CommRingCat.ofHom
      (CoordinateFlagTotalQuotient.equiv R A Sel x v).symm.toRingHom)).op _) = _
  congr 1
  have hh := OrderedAffineFlagEvaluation.full_quotient_affine_evaluation J L G R A Sel x v
    site M N V O hV hAll hZero j ((normal).inv ≫ a)
  simpa only [← Functor.mapIso_hom,Category.assoc,Iso.hom_inv_id_assoc] using hh

include hV in
omit [J.Additive] [L.Additive] [HasZeroObject Z] [HasShift Z ℤ] [J.CommShift ℤ] [L.CommShift ℤ]
  [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive] [Pretriangulated Z] [L.IsTriangulated] in
theorem fiber_evaluation
    (a : L.obj (CoordinatePurityInput.normalThom A Sel x G) ⟶ Coef) :
    ActualSheafContractionRestriction.pullback site (N (j-r))
      (OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI).toRingHom
      (OrderedThomSections.evaluate Sel r hr (GlobalNormalFrame.ZeroLayer R κ n I B)
        J L G R site M N V hZero j a) =
    (O.orientation New (j-r) (-1) ^
      ((Finset.univ.erase v).filter (fun i : Sel => i < v)).card)
      (AffineShiftedThomSections.evaluate J L G R New (Option (CoordinateFlag.Old Sel v)) r
        ((OrderedOptionFlagNumbering.card_count Sel v).trans
          ((OrderedFlagNumbering.card_count Sel v).symm.trans hr)) site M N V hNew j
        ((torusNew).inv ≫ a)) := by
  rw [projection_evaluation J L G R κ n I B v hpos hneg hsupport hI hf hs r hr site M N V hV O j]
  change (N (j-r)).val.map (Spec.map (CommRingCat.ofHom
      (closedProjection R κ n I B v hpos hneg hsupport hI).toRingHom)).op _ = _
  rw [OrientationBaseNaturality.power_naturality J L G R All New site M N V hV O
    (closedProjection R κ n I B v hpos hneg hsupport hI) hAll hNew]
  congr 1
  rw [inverse_torusNormal L G R κ n I B v H hpos hneg hsupport hI hf hs, Category.assoc]
  exact (AffineShiftedThomNaturality.evaluate_naturality J L G R All New
    (Option (CoordinateFlag.Old Sel v)) r
    ((OrderedOptionFlagNumbering.card_count Sel v).trans
      ((OrderedFlagNumbering.card_count Sel v).symm.trans hr))
    (closedProjection R κ n I B v hpos hneg hsupport hI) site M N V hV hAll hNew j
    ((normal).inv ≫ a)).symm


#print axioms selectedOrder
#print axioms optionOrder
#print axioms closedProjection
#print axioms inverse_torusNormal
#print axioms projection_evaluation
#print axioms fiber_evaluation
end Verification.OriginalOrderedFiberEvaluation
