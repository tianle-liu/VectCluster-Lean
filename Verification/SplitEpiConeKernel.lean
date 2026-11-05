/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TransverseDerivedBoundary
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Split Epi Cone Kernel

The actual categorical kernel of an epimorphism of cochain complexes gives
the shifted kernel model of its cone in the derived category. Rotation of
the kernel short exact sequence fixes the sign: the positive projection
from the cone corresponds to the shifted kernel inclusion.
-/
namespace Verification.SplitEpiConeKernel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
variable [HasDerivedCategory.{w} C]
variable {U B : CochainComplex C ℤ} (π : U ⟶ B)

/-- The short complex uses the actual kernel in the category of complexes. -/
noncomputable def kernelSequence : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (kernel.ι π) π (kernel.condition π)

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem kernelSequence_shortExact [Epi π] : (kernelSequence π).ShortExact where
  exact := CategoryTheory.ShortComplex.exact_kernel π
  mono_f := by change Mono (kernel.ι π); infer_instance
  epi_g := by change Epi π; infer_instance

theorem cone_distinguished :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle π) ∈
      distTriang (DerivedCategory C) := by
  rw [DerivedCategory.mem_distTriang_iff]
  exact ⟨_, _, π, ⟨Iso.refl _⟩⟩

variable [Epi π]

/-- Compare the actual cone triangle with the rotated kernel exact triangle. -/
noncomputable def triangleIso :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle π) ≅
      (DerivedCategory.triangleOfSES (kernelSequence_shortExact π)).rotate :=
  isoTriangleOfIso₁₂ _ _ (cone_distinguished π)
    (rot_of_distTriang _ (DerivedCategory.triangleOfSES_distinguished
      (kernelSequence_shortExact π)))
    (Iso.refl _) (Iso.refl _) (by simp [kernelSequence])

/-- The third component is the desired derived isomorphism. -/
noncomputable def coneKernelShiftIso :
    DerivedCategory.Q.obj (mappingCone π) ≅
      (DerivedCategory.Q.obj (kernel π))⟦(1 : ℤ)⟧ :=
  Triangle.π₃.mapIso (triangleIso π)

/-- Positive cone boundary equals the shifted inclusion under this comparison. -/
theorem positive_boundary_shift :
    Verification.TransverseDerivedBoundary.boundary π ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app U =
      (coneKernelShiftIso π).hom ≫
        (DerivedCategory.Q.map (kernel.ι π))⟦(1 : ℤ)⟧' := by
  have h := (triangleIso π).hom.comm₃
  change (DerivedCategory.Q.map (mappingCone.triangle π).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app U) ≫
        (𝟙 (DerivedCategory.Q.obj U))⟦(1 : ℤ)⟧' =
    (coneKernelShiftIso π).hom ≫
      (-(DerivedCategory.Q.map (kernel.ι π))⟦(1 : ℤ)⟧') at h
  rw [CategoryTheory.Functor.map_id] at h
  erw [CategoryTheory.Category.comp_id] at h
  simpa only [Verification.TransverseDerivedBoundary.boundary,
    Verification.TransverseConeBoundary.boundary, Functor.map_neg,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using congrArg Neg.neg h

/-- The same isomorphism with the shifted complex inside the localization. -/
noncomputable def coneKernelIso :
    DerivedCategory.Q.obj (mappingCone π) ≅
      DerivedCategory.Q.obj ((kernel π)⟦(1 : ℤ)⟧) :=
  coneKernelShiftIso π ≪≫ ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app (kernel π)).symm

theorem positive_boundary :
    Verification.TransverseDerivedBoundary.boundary π =
      (coneKernelIso π).hom ≫
        DerivedCategory.Q.map ((kernel.ι π)⟦(1 : ℤ)⟧') := by
  apply (cancel_mono ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app U)).1
  rw [positive_boundary_shift]
  simp only [coneKernelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Functor.commShiftIso_hom_naturality, Iso.inv_hom_id_app_assoc]
  change _ = (coneKernelShiftIso π).hom ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app (kernel π) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (kernel π) ≫ _
  simp only [Iso.inv_hom_id_app_assoc]

theorem inverse_positive_boundary :
    (coneKernelIso π).inv ≫ Verification.TransverseDerivedBoundary.boundary π =
      DerivedCategory.Q.map ((kernel.ι π)⟦(1 : ℤ)⟧') := by
  rw [positive_boundary, Iso.inv_hom_id_assoc]

omit [Epi π] in
/-- A supplied cochain section proves the epimorphism hypothesis internally. -/
noncomputable def splitConeKernelIso (s : B ⟶ U) (hs : s ≫ π = 𝟙 B) :
    DerivedCategory.Q.obj (mappingCone π) ≅
      DerivedCategory.Q.obj ((kernel π)⟦(1 : ℤ)⟧) := by
  letI : Epi π := (SplitEpi.mk s hs).epi
  exact coneKernelIso π

omit [Epi π] in
theorem split_positive_boundary (s : B ⟶ U) (hs : s ≫ π = 𝟙 B) :
    (splitConeKernelIso π s hs).hom ≫
        DerivedCategory.Q.map ((kernel.ι π)⟦(1 : ℤ)⟧') =
      DerivedCategory.Q.map (Verification.TransverseConeBoundary.boundary π) := by
  letI : Epi π := (SplitEpi.mk s hs).epi
  exact (positive_boundary π).symm

omit [Epi π] in
theorem split_inverse_positive_boundary (s : B ⟶ U) (hs : s ≫ π = 𝟙 B) :
    (splitConeKernelIso π s hs).inv ≫
        DerivedCategory.Q.map (Verification.TransverseConeBoundary.boundary π) =
      DerivedCategory.Q.map ((kernel.ι π)⟦(1 : ℤ)⟧') := by
  letI : Epi π := (SplitEpi.mk s hs).epi
  exact inverse_positive_boundary π

end Verification.SplitEpiConeKernel

#print axioms Verification.SplitEpiConeKernel.kernelSequence
#print axioms Verification.SplitEpiConeKernel.kernelSequence_shortExact
#print axioms Verification.SplitEpiConeKernel.cone_distinguished
#print axioms Verification.SplitEpiConeKernel.triangleIso
#print axioms Verification.SplitEpiConeKernel.coneKernelShiftIso
#print axioms Verification.SplitEpiConeKernel.positive_boundary_shift
#print axioms Verification.SplitEpiConeKernel.coneKernelIso
#print axioms Verification.SplitEpiConeKernel.positive_boundary
#print axioms Verification.SplitEpiConeKernel.inverse_positive_boundary
#print axioms Verification.SplitEpiConeKernel.splitConeKernelIso
#print axioms Verification.SplitEpiConeKernel.split_positive_boundary
#print axioms Verification.SplitEpiConeKernel.split_inverse_positive_boundary
