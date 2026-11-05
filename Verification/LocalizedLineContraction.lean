/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedConeComparison
import Verification.SplitEpiConeKernel
import Verification.ActualLineContraction
import Verification.ActualTransversePurity

/-!
# Localized Line Contraction

The actual punctured transverse line has the u=1 section. A¹-invariance
identifies its localization cone with the shifted kernel of this split
projection. The positive boundary is exactly the inclusion of that reduced
summand; no residue formula is assumed.
-/
namespace Verification.LocalizedLineContraction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualTransverseLocalization
open Verification.ExchangeTransverseSlice Verification.ActualTransverseBasepoint
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)

variable [IsIso (L.map (DerivedCategory.Q.map (lineProjection R ι κ τ B F)))]

noncomputable def lineConeIso :
    L.obj (DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.sliceOpen R ι κ τ B F))) ≅
      L.obj (DerivedCategory.Q.obj (mappingCone (projection R ι κ τ B F))) := by
  letI : IsIso (L.map (DerivedCategory.Q.map (𝟙 (F.obj (op (CommRingCat.mkUnder
      (CommRingCat.of R) (OpenTarget R ι κ τ B))))))) := by
    simp only [CategoryTheory.Functor.map_id]
    infer_instance
  exact LocalizedConeComparison.coneIso L _ _ (𝟙 _) (lineProjection R ι κ τ B F)
    (ActualLineContraction.line_square R ι κ τ B F)

theorem lineConeIso_boundary : (lineConeIso R ι κ τ B L F).hom ≫
    L.map (TransverseDerivedBoundary.boundary (projection R ι κ τ B F)) =
      L.map (TransverseDerivedBoundary.boundary (ActualTransverseCone.sliceOpen R ι κ τ B F)) := by
  have h := TransverseDerivedBoundary.boundary_naturality
    (ActualTransverseCone.sliceOpen R ι κ τ B F) (projection R ι κ τ B F)
    (𝟙 _) (lineProjection R ι κ τ B F) (ActualLineContraction.line_square R ι κ τ B F)
  simpa only [Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id] using congrArg (fun f => L.map f) h

noncomputable def contractionIso :
    L.obj (DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.sliceOpen R ι κ τ B F))) ≅
      L.obj (DerivedCategory.Q.obj ((kernel (projection R ι κ τ B F))⟦(1 : ℤ)⟧)) :=
  lineConeIso R ι κ τ B L F ≪≫ L.mapIso (SplitEpiConeKernel.splitConeKernelIso
    (projection R ι κ τ B F) (sectionMap R ι κ τ B F) (section_projection R ι κ τ B F))

theorem contractionIso_boundary : (contractionIso R ι κ τ B L F).hom ≫
    L.map (DerivedCategory.Q.map ((kernel.ι (projection R ι κ τ B F))⟦(1 : ℤ)⟧')) =
      L.map (TransverseDerivedBoundary.boundary (ActualTransverseCone.sliceOpen R ι κ τ B F)) := by
  simp only [contractionIso, Iso.trans_hom, Category.assoc, Functor.mapIso_hom, ← Functor.map_comp,
    SplitEpiConeKernel.split_positive_boundary]
  exact lineConeIso_boundary R ι κ τ B L F

#print axioms lineConeIso
#print axioms lineConeIso_boundary
#print axioms contractionIso
#print axioms contractionIso_boundary
end Verification.LocalizedLineContraction
