/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedFlagPairs

/-!
# Localized Flag Coherence

Uniform ordered-coordinate flag coherence for homotopy purity. This
is an explicit cited-theorem interface on arbitrary smooth framed rings,
not an exchange-matrix differential assumption. Its diagrams are genuine
derived localization triangles. The positive boundary identity is then
extracted from the triangle morphism, including the shift sign.
-/
noncomputable section
namespace Verification.LocalizedFlagCoherence
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag Verification.CoordinatePurityInput
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (R : Type) [CommRing R]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (A ι : Type) [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
variable (x : ι → A) (v : ι)
variable (fullFrame : Frame R A ι x)
variable (oldFrame : Frame R A (Old ι v) (oldCoordinate A ι x v))
variable (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
  (CoordinateLocalizationPair.coordinate A ι x v))

def shiftedIso {U W : CochainComplex C ℤ}
    (e : (DerivedCategory.Q ⋙ L).obj U ≅ (DerivedCategory.Q ⋙ L).obj W) :
    (DerivedCategory.Q ⋙ L).obj (U⟦(1 : ℤ)⟧) ≅ (DerivedCategory.Q ⋙ L).obj (W⟦(1 : ℤ)⟧) :=
  ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app U ≪≫
    (CategoryTheory.shiftFunctor D (1 : ℤ)).mapIso e ≪≫
      (((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app W).symm

structure Comparison where
  iteratedThom : L.obj (normalThom A ι x G) ≅
    (DerivedCategory.Q ⋙ L).obj (mappingCone (RelativeFlagOpenBoundary.openArrow R A ι x v G))
  triangle : (DerivedCategory.Q ⋙ L).mapTriangle.obj
      (mappingConeCompTriangle (firstArrow A ι x v G) (secondArrow A ι x G)) ≅
    (DerivedCategory.Q ⋙ L).mapTriangle.obj (mappingCone.triangle (RelativeFlagOpenBoundary.openArrow R A ι x v G))
  old_eq : triangle.hom.hom₁ = (LocalizedFlagPairs.oldIso L R A ι x v G E P localFrame).hom
  total_eq : triangle.hom.hom₂ = (LocalizedFlagPairs.totalIso L R A ι x v G P oldFrame).hom
  full_eq : triangle.hom.hom₃ = (P.comparison A ι x fullFrame).hom ≫ iteratedThom.hom

variable (K : Comparison L R G E P A ι x v fullFrame oldFrame localFrame)

theorem positive_boundary : (P.comparison A ι x fullFrame).hom ≫ K.iteratedThom.hom ≫
    L.map (TransverseDerivedBoundary.boundary (RelativeFlagOpenBoundary.openArrow R A ι x v G)) =
      L.map (CoordinateFlag.boundary A ι x v G) ≫
        (shiftedIso L (LocalizedFlagPairs.oldIso L R A ι x v G E P localFrame)).hom := by
  have h := K.triangle.hom.comm₃
  rw [K.old_eq,K.full_eq] at h
  change ((DerivedCategory.Q ⋙ L).map (mappingConeCompTriangle (firstArrow A ι x v G)
      (secondArrow A ι x G)).mor₃ ≫ ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app _) ≫
        (LocalizedFlagPairs.oldIso L R A ι x v G E P localFrame).hom⟦(1 : ℤ)⟧' =
      ((P.comparison A ι x fullFrame).hom ≫ K.iteratedThom.hom) ≫
        ((DerivedCategory.Q ⋙ L).map (mappingCone.triangle (RelativeFlagOpenBoundary.openArrow R A ι x v G)).mor₃ ≫
          ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app _) at h
  have hn := congrArg Neg.neg h
  simp only [CoordinateFlag.boundary,TransverseDerivedBoundary.boundary,TransverseConeBoundary.boundary,
    mappingConeCompTriangle_mor₃,Functor.comp_map,Functor.map_neg,Functor.map_comp,
    Preadditive.neg_comp,Preadditive.comp_neg] at hn ⊢
  apply (cancel_mono (((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app _)).1
  dsimp only [shiftedIso,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom]
  simpa only [Functor.comp_obj,Iso.app_hom,Iso.app_inv,Preadditive.neg_comp,Preadditive.comp_neg,
    Category.assoc,Iso.inv_hom_id_app_assoc,Iso.inv_hom_id_app,Iso.inv_hom_id,Category.comp_id] using hn.symm

/-- The standard flag-purity theorem is uniform in ordered coordinates and
contains no cluster data, symbol coefficient, or cellular differential. -/
structure Standard where
  comparison : ∀ (A ι : Type) [CommRing A] [Algebra R A] [Fintype ι] [LinearOrder ι]
    (x : ι → A) (v : ι) (fullFrame : Frame R A ι x)
    (oldFrame : Frame R A (Old ι v) (oldCoordinate A ι x v))
    (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
      (CoordinateLocalizationPair.coordinate A ι x v)),
    Comparison L R G E P A ι x v fullFrame oldFrame localFrame

#print axioms shiftedIso
#print axioms Comparison
#print axioms positive_boundary
#print axioms Standard
end Verification.LocalizedFlagCoherence
