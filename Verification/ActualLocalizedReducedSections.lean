/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedSplitHomContraction
import Verification.ActualTorusBasepointNaturality

/-!
# Actual Localized Reduced Sections

Actual reduced Laurent tests are the kernel of evaluation at u=1.
The actual character-fiber restriction acts on this kernel, and its action
is exactly the previously constructed reduced-kernel map after localization.
-/
noncomputable section
namespace Verification.ActualLocalizedReducedSections
open CategoryTheory CategoryTheory.Limits Opposite
open Verification.ActualOpenChart Verification.ExchangeTransverseSlice
universe u w
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)
variable (L : DerivedCategory C ⥤ D) [L.Additive] (n : ℤ) (M : D)

abbrev sections := (LocalizedSplitHomContraction.atBasepoint (LaurentBasepoint.sectionMap R A F) L n M).ker

def equiv : (L.obj (DerivedCategory.Q.obj
    ((kernel (LaurentBasepoint.projection R A F))⟦n⟧)) ⟶ M) ≃+ sections R A F L n M :=
  LocalizedSplitHomContraction.reducedEquiv (LaurentBasepoint.projection R A F)
    (LaurentBasepoint.sectionMap R A F) (LaurentBasepoint.section_projection R A F) L n M

variable (ι κ τ : Type u) [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι)
local notation "New" => Fiber (characters R ι κ τ B)
local notation "Old" => ActualTorusReducedRestriction.OldBase R ι κ τ B v

def restriction : sections R Old F L n M →+ sections R New F L n M where
  toFun a := ⟨(DerivedCategory.Q ⋙ L).map
    (((F.map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op))⟦n⟧') ≫ a.val, by
      change (DerivedCategory.Q ⋙ L).map ((LaurentBasepoint.sectionMap R New F)⟦n⟧') ≫
        ((DerivedCategory.Q ⋙ L).map ((F.map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op)⟦n⟧') ≫ a.val) = 0
      rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        ActualTorusBasepointNaturality.section_square, Functor.map_comp, Functor.map_comp, Category.assoc]
      have ha : (DerivedCategory.Q ⋙ L).map ((LaurentBasepoint.sectionMap R Old F)⟦n⟧') ≫ a.val = 0 := a.property
      rw [ha, comp_zero]⟩
  map_zero' := by apply Subtype.ext; simp only [AddSubgroup.coe_zero, comp_zero]
  map_add' a b := by apply Subtype.ext; simp only [AddSubgroup.coe_add, Preadditive.comp_add]

omit [Preadditive D] [L.Additive] in
theorem contraction_restriction
    (a : L.obj (DerivedCategory.Q.obj ((F.obj (op (CommRingCat.mkUnder (CommRingCat.of R)
      (LaurentBasepoint.Laurent Old))))⟦n⟧)) ⟶ M) :
    LocalizedSplitHomContraction.contraction (LaurentBasepoint.projection R New F) L n M
      ((DerivedCategory.Q ⋙ L).map ((F.map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op)⟦n⟧') ≫ a) =
    (DerivedCategory.Q ⋙ L).map ((ActualTorusReducedRestriction.reducedRestriction R ι κ τ B v F)⟦n⟧') ≫
      LocalizedSplitHomContraction.contraction (LaurentBasepoint.projection R Old F) L n M a := by
  have h := congrArg (fun f => (DerivedCategory.Q ⋙ L).map (f⟦n⟧'))
    (ActualTorusReducedRestriction.restriction_inclusion R ι κ τ B v F)
  simp only [Functor.map_comp] at h
  simpa only [LocalizedSplitHomContraction.contraction, Category.assoc] using
    congrArg (fun f => f ≫ a) h.symm

theorem equiv_naturality
    (a : L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R Old F))⟦n⟧)) ⟶ M) :
    equiv R New F L n M
      ((DerivedCategory.Q ⋙ L).map ((ActualTorusReducedRestriction.reducedRestriction R ι κ τ B v F)⟦n⟧') ≫ a) =
    restriction R F L n M ι κ τ B v (equiv R Old F L n M a) := by
  apply (equiv R New F L n M).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change _ = LocalizedSplitHomContraction.contraction (LaurentBasepoint.projection R New F) L n M
    ((DerivedCategory.Q ⋙ L).map ((F.map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op)⟦n⟧') ≫
      LocalizedSplitHomContraction.extend (LaurentBasepoint.projection R Old F)
        (LaurentBasepoint.sectionMap R Old F) (LaurentBasepoint.section_projection R Old F) L n M a)
  rw [contraction_restriction, LocalizedSplitHomContraction.contraction_extend]

#print axioms sections
#print axioms equiv
#print axioms restriction
#print axioms contraction_restriction
#print axioms equiv_naturality
end Verification.ActualLocalizedReducedSections
