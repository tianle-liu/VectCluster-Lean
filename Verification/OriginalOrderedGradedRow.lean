/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalOrderedContractionSum
import Verification.OriginalGradedContractionBlocks
import Verification.OriginalOrderedFiberEvaluation
import Verification.OriginalFiberSectionIso
import Verification.AffineThomEvaluationInstances

/-!
# Original Ordered Graded Row

The whole actual coefficient row after the one canonical target
fiber projection. Each summand is the ordinary u=1 contraction of the
source in its actual torus coordinates, followed by the actual fiber
restriction and the proved normal-order orientation power.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalOrderedGradedRow
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable [Nontrivial R] (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)

variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme, IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)

open scoped BigOperators
local notation "Model" => OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty


variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (U : LocalizedAffineThomInvariance.Standard L R G)


variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (Norm : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] [DecidableEq ι] (v : ι) (r : ℕ)
  (hr : Fintype.card (CoordinateFlag.Old ι v) = r),
  StandardThomContractionNormalization.Standard J L G R site M N V hV U
    (CoordinateFlag.Old ι v) r hr (K.principal ι v) Cg)
variable (p : ℕ) (b : ActualCellThom.Index κ n B (p+1)) (v : Selected n b.val)
set_option quotPrecheck false
local notation "Sel" => Selected n b.val
local notation "Rest" => Other n b.val
local notation "Mat" => IndependentChartIndex.matrix κ n b.val B
local notation "Old" => ActualTorusReducedRestriction.OldBase R Sel (Rest ⊕ κ) Rest Mat v
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest Mat)
local notation "I" => ActualGlobalBoundary.edgeIndex κ n B p b v
local notation "hMat" => IndependentChartIndex.matrix_zero_block κ n b.val B hpos hneg hsupport b.property.2
local notation "hsOld" => ActualOldFiberSmooth.old_smooth R Sel (Rest ⊕ κ) Rest Mat v Sum.inl hMat
  (hf b.val b.property.2) (hs b.val b.property.2)

omit [Fintype κ] in
theorem selected_order : ActualNormalizedFlag.selectedOrder n b.val =
    (inferInstance : LinearOrder Sel) := by
  apply LinearOrder.ext
  intro a c
  rfl

def normalization : StandardThomContractionNormalization.Standard J L G R site M N V hV U
    (CoordinateFlag.Old Sel v) p (OriginalGradedContractionBlocks.old_card κ n B p b v)
    (LocalizedActualFlag.principal L R n b.val v G E P K) Cg := by
  have hp : LocalizedActualFlag.principal L R n b.val v G E P K = K.principal Sel v := by
    exact congrArg (fun o : LinearOrder Sel => @K.principal Sel (inferInstance : Fintype Sel) o v)
      (selected_order κ n B p b)
  rw [hp]
  exact Norm Sel v p (OriginalGradedContractionBlocks.old_card κ n B p b v)

def residueValue (j : ℤ)
    (a : (N (j-p)).val.obj (Opposite.op
      (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n (I).val B))))) :
    (N (j-(p+1 : ℕ))).val.obj (Opposite.op (Spec (CommRingCat.of New))) :=
  (O.orientation New (j-(p+1 : ℕ)) (-1) ^
    ((Finset.univ.erase v).filter (fun i : Sel => i < v)).card)
    (ActualSheafContractionRestriction.pullback site (N (j-(p+1 : ℕ)))
      (ActualTorusReducedRestriction.fiberRestriction R Sel (Rest ⊕ κ) Rest Mat v).toRingHom
      (StandardThomContractionNormalization.lower R site N Cg Old hsOld p j
        (OriginalGradedContractionBlocks.oldKernel J L G E R κ n B P hpos hneg hsupport hf hs U p b v
          site M N V hV j
          (StrictPositiveCoefficientTests.suspendTest J p (M j) _
            ((OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs
              site M N V p j I).symm a)))))

include Q hCg Norm in
omit [HasBinaryBiproducts A] [J.Additive] [J.IsTriangulated] in
theorem block_formula (j : ℤ)
    (a : (N (j-p)).val.obj (Opposite.op
      (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n (I).val B))))) :
    ActualSheafContractionRestriction.pullback site (N (j-(p+1 : ℕ)))
      (OriginalCanonicalFiberProjection.projection R κ n b.val B hpos hneg hsupport b.property.2).toRingHom
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs
        site M N V (p+1) j b
        (OriginalStrictContractionBlocks.contractionBlock L G E R κ n B P hpos hneg hsupport hf hs K U p b v ≫
          StrictPositiveCoefficientTests.suspendTest J p (M j) _
            ((OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs
              site M N V p j I).symm a))) =
    residueValue J L G R κ n B hpos hneg hsupport hf hs E P site M N V U hV O Cg p b v j a := by
  rw [← OriginalStrictContractionBlocks.positive_eq_contraction L G E R κ n B P
    hpos hneg hsupport hf hs Q K U p b v]
  change ActualSheafContractionRestriction.pullback site (N _)
    (OriginalCanonicalFiberProjection.projection R κ n b.val B hpos hneg hsupport b.property.2).toRingHom
    (OrderedThomSections.evaluate Sel (p+1) ((Fintype.card_coe b.val).trans b.property.1)
      (GlobalNormalFrame.ZeroLayer R κ n b.val B) J L G R site M N V _ j _) = _
  have he := OriginalOrderedFiberEvaluation.fiber_evaluation J L G R κ n b.val B v U
    hpos hneg hsupport b.property.2 (hf b.val b.property.2) (hs b.val b.property.2)
    (p+1) ((Fintype.card_coe b.val).trans b.property.1) site M N V hV O j
    (OriginalStrictBoundaryGeometry.positiveBlock L G E R κ n B P hpos hneg hsupport hf hs p b I ≫
      StrictPositiveCoefficientTests.suspendTest J p (M j) _
        ((OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs
          site M N V p j I).symm a))
  simp only [OriginalOrderedFiberEvaluation.selectedOrder, selected_order κ n B p b] at he
  convert he.trans ?_ using 1
  try congr 1
  try apply Subsingleton.elim
  have hb := OriginalGradedContractionBlocks.block_evaluation J L G E R κ n B P hpos hneg hsupport hf hs
    Q K U p b v site M N V hV Cg hCg
    (normalization J L G R κ n B E P site M N V K U hV Cg Norm p b v) j
    (StrictPositiveCoefficientTests.suspendTest J p (M j) _
      ((OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs
        site M N V p j I).symm a))
  refine Eq.trans ?_ hb
  change (AffineThomEvaluationInstances.evaluateWith J L G R New (Option (CoordinateFlag.Old Sel v))
    (p+1) site M N V _ j _ _ _) _ =
    (AffineThomEvaluationInstances.evaluateWith J L G R New (Option (CoordinateFlag.Old Sel v))
      (p+1) site M N V _ j _ _ _) _
  apply DFunLike.congr_fun
  apply AffineThomEvaluationInstances.evaluate_instances
  apply LinearOrder.ext
  intro x y
  rfl


include Q hCg Norm in
theorem pulledback_differential (j : ℤ)
    (a : (StrictCoefficientCochains.complex (Model).complex (M j)).X p) :
    ActualSheafContractionRestriction.pullback site (N (j-(p+1 : ℕ)))
      (OriginalCanonicalFiberProjection.projection R κ n b.val B hpos hneg hsupport b.property.2).toRingHom
      (OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
        site M N V (p+1) j ((StrictCoefficientCochains.complex (Model).complex (M j)).d p (p+1) a) b) =
    ∑ v : b.val, residueValue J L G R κ n B hpos hneg hsupport hf hs E P site M N V U hV O Cg p b v j
      (OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
        site M N V p j a (ActualGlobalBoundary.edgeIndex κ n B p b v)) := by
  rw [OriginalOrderedContractionSum.ordered_contraction_sum J L G R T κ n B hpos hneg hsupport hf hs
    E P H empty site M N V Q K U]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact block_formula J L G R κ n B hpos hneg hsupport hf hs E P site M N V Q K U hV O Cg hCg Norm p b v j _

def targetVertex : Selected n b.val := by
  have h : b.val.Nonempty := Finset.card_pos.mp (by rw [b.property.1]; omega)
  exact ⟨b.val.min' h,Finset.min'_mem b.val h⟩

include Q hCg Norm in
theorem differential (j : ℤ)
    (a : (StrictCoefficientCochains.complex (Model).complex (M j)).X p) :
    OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
      site M N V (p+1) j ((StrictCoefficientCochains.complex (Model).complex (M j)).d p (p+1) a) b =
    (OriginalFiberSectionIso.sections J L G R κ n b.val B (targetVertex κ n B p b) U
      hpos hneg hsupport b.property.2 (hf b.val b.property.2) (hs b.val b.property.2)
      (p+1) ((Fintype.card_coe b.val).trans b.property.1) site M N V j).symm
      (∑ v : b.val, residueValue J L G R κ n B hpos hneg hsupport hf hs E P site M N V U hV O Cg p b v j
        (OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
          site M N V p j a (ActualGlobalBoundary.edgeIndex κ n B p b v))) := by
  apply (OriginalFiberSectionIso.sections J L G R κ n b.val B (targetVertex κ n B p b) U
    hpos hneg hsupport b.property.2 (hf b.val b.property.2) (hs b.val b.property.2)
    (p+1) ((Fintype.card_coe b.val).trans b.property.1) site M N V j).injective
  rw [AddEquiv.apply_symm_apply, OriginalFiberSectionIso.sections_apply J L G R κ n b.val B
    (targetVertex κ n B p b) U hpos hneg hsupport b.property.2 (hf b.val b.property.2) (hs b.val b.property.2)
    (p+1) ((Fintype.card_coe b.val).trans b.property.1) site M N V hV j]
  exact pulledback_differential J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V
    Q K U hV O Cg hCg Norm p b j a


#print axioms selected_order
#print axioms normalization
#print axioms residueValue
#print axioms block_formula
#print axioms pulledback_differential
#print axioms targetVertex
#print axioms differential
end Verification.OriginalOrderedGradedRow
