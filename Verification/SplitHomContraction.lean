/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SplitEpiConeReduction

/-!
# Split Hom Contraction

The contraction on coefficient sections is the actual projection of
Hom out of a split complex. The identities establish both its normalization
and the direct-sum decomposition, also after localization and shift.
-/
namespace Verification.SplitHomContraction
open CategoryTheory CategoryTheory.Limits CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
variable {U B : CochainComplex C ℤ} (π : U ⟶ B) (s : B ⟶ U) (hs : s ≫ π = 𝟙 B)
variable (n : ℤ) (M : DerivedCategory C)

noncomputable def contraction (a : DerivedCategory.Q.obj (U⟦n⟧) ⟶ M) :
    DerivedCategory.Q.obj ((kernel π)⟦n⟧) ⟶ M :=
  DerivedCategory.Q.map ((kernel.ι π)⟦n⟧') ≫ a

noncomputable def extend (a : DerivedCategory.Q.obj ((kernel π)⟦n⟧) ⟶ M) :
    DerivedCategory.Q.obj (U⟦n⟧) ⟶ M :=
  DerivedCategory.Q.map ((SplitEpiConeReduction.kernelRetraction π s hs)⟦n⟧') ≫ a

noncomputable def baseExtend (b : DerivedCategory.Q.obj (B⟦n⟧) ⟶ M) :
    DerivedCategory.Q.obj (U⟦n⟧) ⟶ M := DerivedCategory.Q.map (π⟦n⟧') ≫ b

theorem contraction_extend (a : DerivedCategory.Q.obj ((kernel π)⟦n⟧) ⟶ M) :
    contraction π n M (extend π s hs n M a) = a := by
  simp only [contraction,extend,← Category.assoc,← CategoryTheory.Functor.map_comp,
    SplitEpiConeReduction.inclusion_retraction,CategoryTheory.Functor.map_id,Category.id_comp]

theorem contraction_base (b : DerivedCategory.Q.obj (B⟦n⟧) ⟶ M) :
    contraction π n M (baseExtend π n M b) = 0 := by
  simp only [contraction,baseExtend,← Category.assoc,← CategoryTheory.Functor.map_comp,
    kernel.condition,Functor.map_zero,zero_comp]

theorem decomposition (a : DerivedCategory.Q.obj (U⟦n⟧) ⟶ M) :
    a = extend π s hs n M (contraction π n M a) +
      baseExtend π n M (DerivedCategory.Q.map (s⟦n⟧') ≫ a) := by
  simp only [extend,contraction,baseExtend,← Category.assoc,← CategoryTheory.Functor.map_comp,
    SplitEpiConeReduction.retraction_inclusion,Functor.map_sub,
    CategoryTheory.Functor.map_id,Preadditive.sub_comp,Category.id_comp,sub_add_cancel]

#print axioms contraction
#print axioms extend
#print axioms baseExtend
#print axioms contraction_extend
#print axioms contraction_base
#print axioms decomposition
end Verification.SplitHomContraction
