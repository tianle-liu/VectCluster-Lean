/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalCanonicalFiberProjection
import Verification.AffineCoefficientSectionIso
import Verification.IndependentCoordinatePurity
import Verification.ActualSheafContractionRestriction

/-!
# Original Fiber Section Iso

The canonical affine-partner-zero map on the actual original stratum
induces a coefficient-section isomorphism. In particular equality after
this same target projection detects equality in the original coefficient
row, by ordinary affine invariance proved through representability.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalFiberSectionIso
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

variable (r : ℕ) (hr : Fintype.card (Selected n I) = r)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A₀) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (j : ℤ)

def sections :
    (N (j-r)).val.obj (op (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B)))) ≃+
      (N (j-r)).val.obj (op (Spec (CommRingCat.of New))) :=
  AffineCoefficientSectionIso.sections J L G R (GlobalNormalFrame.ZeroLayer R κ n I B) New Sel Sel
    (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI)
    hZero hNew H r hr site M N V j

include hV in
omit [J.Additive] [L.Additive] [J.CommShift ℤ] [L.CommShift ℤ] [HasShift Z ℤ] [HasZeroObject Z]
  [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive] [Pretriangulated Z] [L.IsTriangulated] [Nontrivial R] in
theorem sections_apply
    (a : (N (j-r)).val.obj (op (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B))))) :
    sections J L G R κ n I B v H hpos hneg hsupport hI hf hs r hr site M N V j a =
    ActualSheafContractionRestriction.pullback site (N (j-r))
      (OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI).toRingHom a := by
  exact AffineCoefficientSectionIso.sections_apply J L G R
    (GlobalNormalFrame.ZeroLayer R κ n I B) New Sel Sel
    (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI)
    hZero hNew H r hr site M N V hV j a

include hV H hf hs hr v in
omit [J.Additive] [L.Additive] [J.CommShift ℤ] [L.CommShift ℤ] [HasShift Z ℤ] [HasZeroObject Z]
  [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive] [Pretriangulated Z] [L.IsTriangulated] [Nontrivial R] in
theorem pullback_injective : Function.Injective
    (ActualSheafContractionRestriction.pullback site (N (j-r))
      (OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI).toRingHom) := by
  intro a b hab
  apply (sections J L G R κ n I B v H hpos hneg hsupport hI hf hs r hr site M N V j).injective
  simpa only [sections_apply J L G R κ n I B v H hpos hneg hsupport hI hf hs r hr site M N V hV j] using hab

#print axioms sections
#print axioms sections_apply
#print axioms pullback_injective
end Verification.OriginalFiberSectionIso
