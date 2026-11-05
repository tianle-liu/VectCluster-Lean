/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SplitEpiConeKernel

/-!
# Split Epi Cone Reduction

The derived comparison is induced by an explicit cochain map:
positive cone projection followed by the retraction onto the actual kernel.
The section removes the base summand by the idempotent `1 - π ≫ s`.
-/
namespace Verification.SplitEpiConeReduction

open CategoryTheory CategoryTheory.Limits CochainComplex

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {U B : CochainComplex C ℤ} (π : U ⟶ B) (s : B ⟶ U)
variable (hs : s ≫ π = 𝟙 B)

noncomputable def kernelRetraction : U ⟶ kernel π :=
  kernel.lift π (𝟙 U - π ≫ s) (by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hs,
      Category.comp_id, sub_self])

theorem retraction_inclusion :
    kernelRetraction π s hs ≫ kernel.ι π = 𝟙 U - π ≫ s := by
  exact kernel.lift_ι _ _ _

theorem inclusion_retraction :
    kernel.ι π ≫ kernelRetraction π s hs = 𝟙 (kernel π) := by
  apply (cancel_mono (kernel.ι π)).1
  rw [Category.assoc, retraction_inclusion, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, kernel.condition,
    zero_comp, sub_zero, Category.id_comp]

variable [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]

/-- Actual cochain-level comparison, before derived localization. -/
noncomputable def comparison :
    mappingCone π ⟶ (kernel π)⟦(1 : ℤ)⟧ :=
  Verification.TransverseConeBoundary.boundary π ≫
    (kernelRetraction π s hs)⟦(1 : ℤ)⟧'

theorem comparison_eq_iso :
    DerivedCategory.Q.map (comparison π s hs) =
      (Verification.SplitEpiConeKernel.splitConeKernelIso π s hs).hom := by
  have h := Verification.SplitEpiConeKernel.split_positive_boundary π s hs
  rw [comparison, CategoryTheory.Functor.map_comp, ← h]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, inclusion_retraction,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The explicit comparison is a genuine quasi-isomorphism. -/
theorem comparison_quasiIso : QuasiIso (comparison π s hs) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso C _).1
  rw [comparison_eq_iso]
  infer_instance

/-- This equality takes place in the actual derived category. -/
theorem comparison_positive_boundary :
    DerivedCategory.Q.map (comparison π s hs) ≫
        DerivedCategory.Q.map ((kernel.ι π)⟦(1 : ℤ)⟧') =
      DerivedCategory.Q.map (Verification.TransverseConeBoundary.boundary π) := by
  rw [comparison_eq_iso]
  exact Verification.SplitEpiConeKernel.split_positive_boundary π s hs

end Verification.SplitEpiConeReduction

#print axioms Verification.SplitEpiConeReduction.kernelRetraction
#print axioms Verification.SplitEpiConeReduction.retraction_inclusion
#print axioms Verification.SplitEpiConeReduction.inclusion_retraction
#print axioms Verification.SplitEpiConeReduction.comparison
#print axioms Verification.SplitEpiConeReduction.comparison_eq_iso
#print axioms Verification.SplitEpiConeReduction.comparison_quasiIso
#print axioms Verification.SplitEpiConeReduction.comparison_positive_boundary
