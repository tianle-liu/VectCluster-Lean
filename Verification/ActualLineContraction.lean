/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ConeDerivedComparison
import Verification.SplitEpiConeKernel
import Verification.ActualContractionSplitting
import Verification.ActualTransversePurity

/-!
# Actual Line Contraction

The actual punctured transverse line has the u=1 section. A¹-invariance
identifies its localization cone with the shifted kernel of this split
projection. The positive boundary is exactly the inclusion of that reduced
summand; no residue formula is assumed.
-/
namespace Verification.ActualLineContraction
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualTransverseLocalization
open Verification.ExchangeTransverseSlice Verification.ActualTransverseBasepoint
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable {D : Type*} [Category D] [Abelian D] [HasBinaryBiproducts D] [HasDerivedCategory.{w} D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)

omit [HasDerivedCategory D] in
theorem line_square : ActualTransverseCone.sliceOpen R ι κ τ B F ≫
    lineProjection R ι κ τ B F = (𝟙 _) ≫ projection R ι κ τ B F := by
  rw [Category.id_comp, open_line_projection]

variable [IsIso (DerivedCategory.Q.map (lineProjection R ι κ τ B F))]

noncomputable def lineConeIso :
    DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.sliceOpen R ι κ τ B F)) ≅
      DerivedCategory.Q.obj (mappingCone (projection R ι κ τ B F)) := by
  letI : IsIso (DerivedCategory.Q.map (𝟙 (F.obj (op (CommRingCat.mkUnder
      (CommRingCat.of R) (OpenTarget R ι κ τ B)))))) := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  exact ConeDerivedComparison.coneIso _ _ (𝟙 _) (lineProjection R ι κ τ B F)
    (line_square R ι κ τ B F)

theorem lineConeIso_boundary : (lineConeIso R ι κ τ B F).hom ≫
    TransverseDerivedBoundary.boundary (projection R ι κ τ B F) =
      TransverseDerivedBoundary.boundary (ActualTransverseCone.sliceOpen R ι κ τ B F) := by
  have h := TransverseDerivedBoundary.boundary_naturality
    (ActualTransverseCone.sliceOpen R ι κ τ B F) (projection R ι κ τ B F)
    (𝟙 _) (lineProjection R ι κ τ B F) (line_square R ι κ τ B F)
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using h

noncomputable def contractionIso :
    DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.sliceOpen R ι κ τ B F)) ≅
      DerivedCategory.Q.obj ((kernel (projection R ι κ τ B F))⟦(1 : ℤ)⟧) :=
  lineConeIso R ι κ τ B F ≪≫ SplitEpiConeKernel.splitConeKernelIso
    (projection R ι κ τ B F) (sectionMap R ι κ τ B F) (section_projection R ι κ τ B F)

theorem contractionIso_boundary : (contractionIso R ι κ τ B F).hom ≫
    DerivedCategory.Q.map ((kernel.ι (projection R ι κ τ B F))⟦(1 : ℤ)⟧') =
      TransverseDerivedBoundary.boundary (ActualTransverseCone.sliceOpen R ι κ τ B F) := by
  simp only [contractionIso, Iso.trans_hom, Category.assoc,
    SplitEpiConeKernel.split_positive_boundary]
  exact lineConeIso_boundary R ι κ τ B F

variable [Fintype ι] (j : τ → κ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D)
variable (P : ActualTransversePurity.PurityComparison R ι κ τ j B hB v F T)

noncomputable def thomContractionIso :
    T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ≅
      DerivedCategory.Q.obj ((kernel (projection R ι κ τ B F))⟦(1 : ℤ)⟧) :=
  Arrow.leftFunc.mapIso P ≪≫ contractionIso R ι κ τ B F

theorem actual_slice_contraction : ActualTransversePurity.sliceBoundary R ι κ τ j B hB v F T P =
    (thomContractionIso R ι κ τ B F j hB v T P).hom ≫
      DerivedCategory.Q.map ((kernel.ι (projection R ι κ τ B F))⟦(1 : ℤ)⟧') := by
  simp only [thomContractionIso, Iso.trans_hom, Category.assoc, contractionIso_boundary]
  rfl

#print axioms line_square
#print axioms lineConeIso
#print axioms lineConeIso_boundary
#print axioms contractionIso
#print axioms contractionIso_boundary
#print axioms thomContractionIso
#print axioms actual_slice_contraction
end Verification.ActualLineContraction
