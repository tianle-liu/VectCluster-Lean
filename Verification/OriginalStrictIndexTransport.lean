/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictBlockSections
import Verification.OriginalZeroLayerCast
import Verification.GradedMilnorWittSheaf

/-!
# Original Strict Index Transport

Equality reindexing of actual strata commutes with the true section evaluation.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalStrictIndexTransport
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

attribute [local instance] Abelian.hasFiniteBiproducts

local notation "Model" => OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty


variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)


variable (q : ℕ) (a b : ActualCellThom.Index κ n B q) (h : a=b)
variable (j : ℤ)

omit [HasBinaryBiproducts A] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [HasFiniteBiproducts D] [J.CommShift ℤ] [J.IsTriangulated]
  [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] [Nontrivial R] [HasShift D ℤ] in
theorem section_cast
    (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q a).term ⟶ M j) :
    ActualSheafContractionRestriction.pullback site (N (j-q))
      (OriginalZeroLayerCast.equiv R κ n B (congrArg Subtype.val h)).toRingHom
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V q j a
        (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q a) (M j) f)) =
    OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V q j b
      (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q b) (M j)
        (eqToHom (congrArg (fun i => (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i).term) h.symm) ≫ f)) := by
  subst b
  simp only [eqToHom_refl,Category.id_comp]
  change (N (j-q)).val.map (Spec.map (𝟙 (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n a.val B)))).op _ = _
  simp only [Spec.map_id,op_id]
  rw [(N (j-q)).val.map_id]
  rfl

variable (W : GradedMilnorWittSheaf.Standard site N)

omit [HasBinaryBiproducts A] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [HasFiniteBiproducts D] [J.CommShift ℤ] [J.IsTriangulated]
  [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] [Nontrivial R] [HasShift D ℤ] in
theorem total_cast
    (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q a).term ⟶ M j) :
    GradedMilnorWittSheaf.pullback site N W
      (S:=CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n a.val B))
      (T:=CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n b.val B))
      (OriginalZeroLayerCast.equiv R κ n B (congrArg Subtype.val h)).toRingHom
      (GradedSectionTotal.includeDegree (W.grading (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n a.val B))) (j-q)
        (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V q j a
          (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q a) (M j) f))) =
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n b.val B))) (j-q)
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V q j b
        (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q b) (M j)
          (eqToHom (congrArg (fun i => (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i).term) h.symm) ≫ f))) := by
  rw [GradedMilnorWittSheaf.pullback_degree,section_cast J L G R T κ n B hpos hneg hsupport hf hs site M N V q a b h j f]

#print axioms section_cast
#print axioms total_cast
end Verification.OriginalStrictIndexTransport
