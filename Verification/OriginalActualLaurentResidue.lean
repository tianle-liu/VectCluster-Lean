/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalOrderedGradedRow
import Verification.OriginalSourceReducedKernel
import Verification.GradedMilnorWittResidueNaturality

/-!
# Original Actual Laurent Residue

The genuine adjacent source residue is the ordinary Laurent coefficient
residue of its actual source-ring pullback. In degree zero the normal-order
orientation exponent is proved to vanish, giving the literal Laurent rule.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalActualLaurentResidue
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


variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (O : ThomPermutationInput.Standard J L G R site M N V)

open Verification.SheafGradedLaurentResidue

def sourceMap : GlobalNormalFrame.ZeroLayer R κ n (I).val B →ₐ[R]
    LaurentBasepoint.Laurent New :=
  (ActualTorusFace.torusFace R Sel (Rest ⊕ κ) Rest D v).comp
    (OriginalSourceCoefficientCoordinates.torusMap R κ n t.val B v hD)

include hV in
omit [J.Additive] [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [L.IsTriangulated] in
theorem kernel_formula (j : ℤ)
    (a : Section site N (GlobalNormalFrame.ZeroLayer R κ n (I).val B) (j-p)) :
    OriginalGradedContractionBlocks.oldKernel J L G E R κ n B P hpos hneg hsupport hf hs H p t v
      site M N V hV j (StrictPositiveCoefficientTests.suspendTest J p (M j) _
        ((OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs
          site M N V p j I).symm a)) =
    reduce R Old site N (j-p) (ActualSheafContractionRestriction.pullback site (N (j-p))
      (OriginalSourceCoefficientCoordinates.torusMap R κ n t.val B v hD).toRingHom a) := by
  apply kernel_eq_reduce
  have hh := OriginalSourceReducedKernel.oldKernel_value J L G E R κ n B P hpos hneg hsupport hf hs
    H p t v site M N V hV j
    ((OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs
      site M N V p j I).symm a)
  simpa only [AddEquiv.apply_symm_apply] using hh

include hCg in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [J.Additive] [L.IsTriangulated] in
theorem residue_formula (j : ℤ)
    (a : Section site N (GlobalNormalFrame.ZeroLayer R κ n (I).val B) (j-p)) :
    OriginalOrderedGradedRow.residueValue J L G R κ n B hpos hneg hsupport hf hs E P
      site M N V H hV O Cg p t v j a =
    (O.orientation New (j-(p+1 : ℕ)) (-1) ^
      ((Finset.univ.erase v).filter (fun i : Sel => i<v)).card)
      (StandardThomContractionNormalization.degreeCast site N New ((j-p)-1) (j-(p+1 : ℕ)) (by omega)
        (degreeResidue R New site N Cg hsNew (j-p)
          (ActualSheafContractionRestriction.pullback site (N (j-p))
            (sourceMap R κ n B hpos hneg hsupport p t v).toRingHom a))) := by
  unfold OriginalOrderedGradedRow.residueValue
  rw [kernel_formula J L G E R κ n B P hpos hneg hsupport hf hs H p t v site M N V hV]
  congr 1
  change ActualSheafContractionRestriction.pullback site (N (j-(p+1 : ℕ)))
    (ActualTorusReducedRestriction.fiberRestriction R Sel (Rest ⊕ κ) Rest D v).toRingHom
    (StandardThomContractionNormalization.degreeCast site N Old _ _ _
      (degreeResidue R Old site N Cg hsOld (j-p) _)) = _
  rw [← SheafContractionNaturality.degreeCast_naturality R site N Old New
    (ActualTorusReducedRestriction.fiberRestriction R Sel (Rest ⊕ κ) Rest D v)]
  congr 1
  rw [← GradedMilnorWittResidueNaturality.degree_naturality R Old New site N
    (ActualTorusReducedRestriction.fiberRestriction R Sel (Rest ⊕ κ) Rest D v) Cg hCg hsOld hsNew]
  rw [← ActualLaurentSheafBaseChange.torusFace_eq]
  change degreeResidue R New site N Cg hsNew (j-p)
    ((ActualSheafContractionRestriction.pullback site (N (j-p))
      (ActualTorusFace.torusFace R Sel (Rest ⊕ κ) Rest D v).toRingHom).comp
      (ActualSheafContractionRestriction.pullback site (N (j-p))
        (OriginalSourceCoefficientCoordinates.torusMap R κ n t.val B v hD).toRingHom) a) = _
  rw [← ActualSheafContractionRestriction.pullback_comp]
  rfl

omit [Fintype κ] in
theorem single_preceding_empty (b : ActualCellThom.Index κ n B 1) (v : Selected n b.val) :
    ((Finset.univ.erase v).filter (fun i : Selected n b.val => i<v)) = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro i hi
  have he : i=v := Subtype.ext (Finset.card_le_one.mp (by rw [b.property.1]) i.val i.property v.val v.property)
  exact (Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1 he

include hCg in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [J.Additive] [L.IsTriangulated] in
theorem single_residue (b : ActualCellThom.Index κ n B 1) (v : Selected n b.val) (j : ℤ)
    (a : Section site N
      (GlobalNormalFrame.ZeroLayer R κ n (ActualGlobalBoundary.edgeIndex κ n B 0 b v).val B) (j-(0:ℕ))) :
    OriginalOrderedGradedRow.residueValue J L G R κ n B hpos hneg hsupport hf hs E P
      site M N V H hV O Cg 0 b v j a =
    StandardThomContractionNormalization.degreeCast site N
      (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n b.val)
        (Other n b.val ⊕ κ) (Other n b.val) (matrix κ n b.val B)))
      ((j-(0:ℕ))-1) (j-(0+1:ℕ)) (by omega)
      (degreeResidue R
        (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n b.val)
          (Other n b.val ⊕ κ) (Other n b.val) (matrix κ n b.val B)))
        site N Cg
        (ActualTransversePairSmooth.pair_smooth_AS R (Selected n b.val) (Other n b.val ⊕ κ)
          (Other n b.val) Sum.inl (matrix κ n b.val B)
          (matrix_zero_block κ n b.val B hpos hneg hsupport b.property.2)
          (hf b.val b.property.2) (hs b.val b.property.2) v).1 (j-(0:ℕ))
        (ActualSheafContractionRestriction.pullback site (N (j-(0:ℕ)))
          (sourceMap R κ n B hpos hneg hsupport 0 b v).toRingHom a)) := by
  have hh := residue_formula J L G E R κ n B P hpos hneg hsupport hf hs H 0 b v
    site M N V hV Cg hCg O j a
  rw [single_preceding_empty κ n B b v,Finset.card_empty,pow_zero,Module.End.one_apply] at hh
  exact hh


open scoped DirectSum
open Verification.GradedSectionTotal
variable (b : ActualCellThom.Index κ n B 1) (v₀ : Selected n b.val)
local notation "N₀" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n b.val)
  (Other n b.val ⊕ κ) (Other n b.val) (matrix κ n b.val B))
local notation "s₀" => (ActualTransversePairSmooth.pair_smooth_AS R (Selected n b.val) (Other n b.val ⊕ κ)
  (Other n b.val) Sum.inl (matrix κ n b.val B)
  (matrix_zero_block κ n b.val B hpos hneg hsupport b.property.2)
  (hf b.val b.property.2) (hs b.val b.property.2) v₀).1
variable {A₀ B₀ : Type*} [Ring A₀] [Ring B₀]
variable (E₀ : (⨁ q,Section site N
  (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n b.val)
    (Other n b.val ⊕ κ) (Other n b.val) (matrix κ n b.val B))) q) ≃+ B₀)
variable (EL₀ : (⨁ q,Section site N (LaurentBasepoint.Laurent
  (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n b.val)
    (Other n b.val ⊕ κ) (Other n b.val) (matrix κ n b.val B)))) q) ≃+ A₀)

include hCg in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [J.Additive] [L.IsTriangulated] in
theorem total_single (j : ℤ)
    (a : Section site N
      (GlobalNormalFrame.ZeroLayer R κ n (ActualGlobalBoundary.edgeIndex κ n B 0 b v₀).val B) (j-(0:ℕ))) :
    includeDegree E₀ (j-(0+1:ℕ))
      (OriginalOrderedGradedRow.residueValue J L G R κ n B hpos hneg hsupport hf hs E P
        site M N V H hV O Cg 0 b v₀ j a) =
    totalResidue R N₀ site N Cg s₀ E₀ EL₀
      (includeDegree EL₀ (j-(0:ℕ))
        (ActualSheafContractionRestriction.pullback site (N (j-(0:ℕ)))
          (sourceMap R κ n B hpos hneg hsupport 0 b v₀).toRingHom a)) := by
  rw [single_residue J L G E R κ n B P hpos hneg hsupport hf hs H 0 b site M N V hV Cg hCg O,
    MilnorWittGradedLaurentNormalization.includeDegree_cast,totalResidue_degree]
  rfl

#print axioms sourceMap
#print axioms kernel_formula
#print axioms residue_formula
#print axioms single_preceding_empty
#print axioms single_residue
#print axioms total_single
end Verification.OriginalActualLaurentResidue
