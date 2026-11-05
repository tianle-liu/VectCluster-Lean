/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SplitHomContraction

/-!
# Localized Split Hom Contraction

The actual split-kernel contraction survives an additive localization.
Its target Hom group is internally identified with the kernel of basepoint
evaluation, without requiring the localization to preserve arbitrary kernels.
-/
noncomputable section
namespace Verification.LocalizedSplitHomContraction
open CategoryTheory CategoryTheory.Limits CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
variable {U B : CochainComplex C ℤ} (π : U ⟶ B) (s : B ⟶ U) (hs : s ≫ π = 𝟙 B)

omit [HasDerivedCategory C] in
theorem section_retraction : s ≫ SplitEpiConeReduction.kernelRetraction π s hs = 0 := by
  apply (cancel_mono (kernel.ι π)).mp
  rw [Category.assoc, SplitEpiConeReduction.retraction_inclusion, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, hs, Category.id_comp, sub_self, zero_comp]

variable {D : Type*} [Category D] [Preadditive D]
variable (L : DerivedCategory C ⥤ D) [L.Additive] (n : ℤ) (M : D)

def contraction (a : L.obj (DerivedCategory.Q.obj (U⟦n⟧)) ⟶ M) :
    L.obj (DerivedCategory.Q.obj ((kernel π)⟦n⟧)) ⟶ M :=
  (DerivedCategory.Q ⋙ L).map ((kernel.ι π)⟦n⟧') ≫ a

def extend (a : L.obj (DerivedCategory.Q.obj ((kernel π)⟦n⟧)) ⟶ M) :
    L.obj (DerivedCategory.Q.obj (U⟦n⟧)) ⟶ M :=
  (DerivedCategory.Q ⋙ L).map ((SplitEpiConeReduction.kernelRetraction π s hs)⟦n⟧') ≫ a

def baseExtend (a : L.obj (DerivedCategory.Q.obj (B⟦n⟧)) ⟶ M) :
    L.obj (DerivedCategory.Q.obj (U⟦n⟧)) ⟶ M :=
  (DerivedCategory.Q ⋙ L).map (π⟦n⟧') ≫ a

def atBasepoint : (L.obj (DerivedCategory.Q.obj (U⟦n⟧)) ⟶ M) →+
    (L.obj (DerivedCategory.Q.obj (B⟦n⟧)) ⟶ M) where
  toFun a := (DerivedCategory.Q ⋙ L).map (s⟦n⟧') ≫ a
  map_zero' := comp_zero
  map_add' _ _ := by simp only [Preadditive.comp_add]

omit [Preadditive D] [L.Additive] in
theorem contraction_extend (a : L.obj (DerivedCategory.Q.obj ((kernel π)⟦n⟧)) ⟶ M) :
    contraction π L n M (extend π s hs L n M a) = a := by
  simp only [contraction, extend, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    SplitEpiConeReduction.inclusion_retraction, CategoryTheory.Functor.map_id, Functor.comp_obj, Category.id_comp]

theorem contraction_base (a : L.obj (DerivedCategory.Q.obj (B⟦n⟧)) ⟶ M) :
    contraction π L n M (baseExtend π L n M a) = 0 := by
  simp only [contraction, baseExtend, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    kernel.condition, Functor.map_zero, zero_comp]

theorem decomposition (a : L.obj (DerivedCategory.Q.obj (U⟦n⟧)) ⟶ M) :
    a = extend π s hs L n M (contraction π L n M a) +
      baseExtend π L n M (atBasepoint s L n M a) := by
  simp only [extend, contraction, baseExtend, atBasepoint, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    SplitEpiConeReduction.retraction_inclusion, Functor.map_sub,
    CategoryTheory.Functor.map_id, Functor.comp_obj, Preadditive.sub_comp, Category.id_comp, sub_add_cancel]

theorem basepoint_extend (a : L.obj (DerivedCategory.Q.obj ((kernel π)⟦n⟧)) ⟶ M) :
    atBasepoint s L n M (extend π s hs L n M a) = 0 := by
  change ((DerivedCategory.Q ⋙ L).map (s⟦n⟧')) ≫
    ((DerivedCategory.Q ⋙ L).map ((SplitEpiConeReduction.kernelRetraction π s hs)⟦n⟧') ≫ a) = 0
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, section_retraction]
  simp only [Functor.map_zero, zero_comp]

def reducedEquiv : (L.obj (DerivedCategory.Q.obj ((kernel π)⟦n⟧)) ⟶ M) ≃+
    (atBasepoint s L n M).ker where
  toFun a := ⟨extend π s hs L n M a, basepoint_extend π s hs L n M a⟩
  invFun a := contraction π L n M a.val
  left_inv := contraction_extend π s hs L n M
  right_inv a := by
    apply Subtype.ext
    have h := decomposition π s hs L n M a.val
    have ha : atBasepoint s L n M a.val = 0 := a.property
    rw [ha] at h
    simpa only [baseExtend, comp_zero, add_zero] using h.symm
  map_add' a b := by
    apply Subtype.ext
    change extend π s hs L n M (a+b) = extend π s hs L n M a + extend π s hs L n M b
    simp only [extend, Preadditive.comp_add]

#print axioms section_retraction
#print axioms contraction
#print axioms extend
#print axioms baseExtend
#print axioms atBasepoint
#print axioms contraction_extend
#print axioms contraction_base
#print axioms decomposition
#print axioms basepoint_extend
#print axioms reducedEquiv
end Verification.LocalizedSplitHomContraction
