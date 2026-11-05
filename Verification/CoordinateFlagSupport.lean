/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateLocalizationPair
import Verification.NestedConeBoundary

/-!
# Coordinate Flag Support

The ordinary support arrow of a coordinate flag is the actual map of
coordinate pairs induced by A → A[x_v⁻¹], after the proved excision iso.
This identifies the arrow to which purity naturality applies, without
assuming a residue or a cellular differential formula.
-/
noncomputable section
namespace Verification.CoordinateFlagSupport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag Verification.CoordinatePurityInput
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (A ι : Type) [CommRing A] (x : ι → A) (v : ι)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem composite_arrow : firstArrow A ι x v G ≫ secondArrow A ι x G =
    pairArrow A (Old ι v) (oldCoordinate A ι x v) G := by
  simp only [firstArrow, secondArrow, pairArrow, ← CategoryTheory.Functor.map_comp,
    open_triangle]
  rfl

def totalIso : DerivedCategory.Q.obj (mappingCone (firstArrow A ι x v G ≫ secondArrow A ι x G)) ≅
    relative A (Old ι v) (oldCoordinate A ι x v) G :=
  ConeDerivedComparison.coneIso _ _ (𝟙 _) (𝟙 _) (by simp only [Category.comp_id, Category.id_comp, composite_arrow])

theorem puncture_factor : (CoordinateLocalizationPair.punctureIso A ι x v).hom ≫
    (Spec (CommRingCat.of A)).homOfLE (inf_le_left : oldComplement A ι x v ⊓
      CoordinateLocalizationPair.chart A ι x v ≤ oldComplement A ι x v) =
      CoordinatePairMap.punctureMap (oldCoordinate A ι x v)
        (CoordinateLocalizationPair.coordinate A ι x v) (algebraMap A _) (fun _ => rfl) := by
  rw [← cancel_mono (oldComplement A ι x v).ι]
  rw [Category.assoc, Scheme.homOfLE_ι]
  change _ = _ ≫ (puncture A (Old ι v) (oldCoordinate A ι x v)).ι
  rw [← CoordinatePairMap.puncture_square]
  simp only [CoordinateLocalizationPair.punctureIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]
  rfl

theorem ambient_factor : (CoordinateLocalizationPair.ambientIso A ι x v).hom ≫
    (Spec (CommRingCat.of A)).homOfLE (CoordinateFlagExcision.principal_le A ι x v) ≫
      fullToAmbient A ι x = CoordinateLocalizationPair.inclusion A ι x v := by
  rw [fullToAmbient, Scheme.homOfLE_ι, CoordinateLocalizationPair.ambientIso_inclusion]

theorem ordinary_square : (CoordinateLocalizationPair.oldRelativeIso A ι x v G E).hom ≫
    DerivedCategory.Q.map (NestedConeBoundary.supportMap (firstArrow A ι x v G)
      (secondArrow A ι x G)) ≫ (totalIso A ι x v G).hom =
    CoordinatePairMap.relativeMap (oldCoordinate A ι x v)
      (CoordinateLocalizationPair.coordinate A ι x v) (algebraMap A _) (fun _ => rfl) G := by
  simp only [CoordinateLocalizationPair.oldRelativeIso, Iso.trans_hom,
    CoordinateLocalizationPair.relativeIso, CoordinateFlagExcision.relativeIso,
    OpenOneExcision.relativeIso, ConeDerivedComparison.coneIso, asIso_hom,
    OpenOneExcision.localMap, OpenConeExcision.localMap, totalIso,
    CoordinatePairMap.relativeMap, TransverseDerivedBoundary.coneMap,
    TransverseConeBoundary.coneMap, NestedConeBoundary.supportMap, mappingConeCompTriangle_mor₁]
  simp only [← CategoryTheory.Functor.map_comp, ← mappingCone.map_comp, Category.comp_id]
  apply congrArg DerivedCategory.Q.map
  change mappingCone.map _ _ _ _ _ ≫ mappingCone.map _ _ _ _ _ = _
  rw [← mappingCone.map_comp]
  congr 1
  · change (G.map (CoordinateLocalizationPair.punctureIso A ι x v).hom ≫
      G.map ((Spec (CommRingCat.of A)).homOfLE inf_le_left)) ≫ 𝟙 _ = _
    rw [Category.comp_id, ← CategoryTheory.Functor.map_comp]
    exact congrArg G.map (puncture_factor A ι x v)
  · change (G.map (CoordinateLocalizationPair.ambientIso A ι x v).hom ≫
      G.map ((Spec (CommRingCat.of A)).homOfLE (CoordinateFlagExcision.principal_le A ι x v))) ≫
        G.map (fullToAmbient A ι x) = _
    simp only [← CategoryTheory.Functor.map_comp, Category.assoc]
    exact congrArg G.map (ambient_factor A ι x v)

#print axioms composite_arrow
#print axioms totalIso
#print axioms puncture_factor
#print axioms ambient_factor
#print axioms ordinary_square
end Verification.CoordinateFlagSupport
