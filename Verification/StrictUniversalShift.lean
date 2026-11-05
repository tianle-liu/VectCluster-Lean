/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictTriangleHom

/-!
# Strict Universal Shift

Strict representability is stable under shifts by the actual shift
comparison. Only the shift autoequivalences are fully faithful; no such
hypothesis is imposed on the realization J.
-/
noncomputable section
namespace Verification.StrictUniversalShift
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Verification.StrictTriangleHom
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D]
variable (J : C ⥤ D) [J.Additive]
variable {P : C} {X : D} (φ : X ⟶ J.obj P)

theorem target_iso {E F : C} (e : E ≅ F)
    (h : Function.Bijective (comparison J φ E)) :
    Function.Bijective (comparison J φ F) := by
  constructor
  · intro f g hfg
    apply (cancel_mono e.inv).mp
    apply h.1
    change φ ≫ J.map (f ≫ e.inv) = φ ≫ J.map (g ≫ e.inv)
    rw [J.map_comp, J.map_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun a => a ≫ J.map e.inv) hfg
  · intro u
    obtain ⟨f,hf⟩ := h.2 (u ≫ J.map e.inv)
    refine ⟨f ≫ e.hom, ?_⟩
    change φ ≫ J.map (f ≫ e.hom) = u
    rw [J.map_comp, ← Category.assoc]
    change comparison J φ E f ≫ J.map e.hom = u
    rw [hf, Category.assoc, ← J.map_comp, e.inv_hom_id, J.map_id, Category.comp_id]

variable [HasShift C ℤ] [HasShift D ℤ] [J.CommShift ℤ]

theorem shifted_comparison (E : C) (n : ℤ) (f : P ⟶ E) :
    comparison J (shifted J φ n) (E⟦n⟧) (f⟦n⟧') ≫ (J.commShiftIso n).hom.app E =
      (comparison J φ E f)⟦n⟧' := by
  change ((φ⟦n⟧' ≫ (J.commShiftIso n).inv.app P) ≫ J.map (f⟦n⟧')) ≫
    (J.commShiftIso n).hom.app E = (φ ≫ J.map f)⟦n⟧'
  rw [Category.assoc, J.commShiftIso_hom_naturality]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]

theorem bijective_on_shifted_target (h : Universal J φ) (E : C) (n : ℤ) :
    Function.Bijective (comparison J (shifted J φ n) (E⟦n⟧)) := by
  constructor
  · intro f g hfg
    obtain ⟨f₀,rfl⟩ := (shiftFunctor C n).map_surjective f
    obtain ⟨g₀,rfl⟩ := (shiftFunctor C n).map_surjective g
    congr 1
    apply (h E).1
    apply (shiftFunctor D n).map_injective
    rw [← shifted_comparison J φ E n f₀, ← shifted_comparison J φ E n g₀, hfg]
  · intro u
    obtain ⟨u₀,hu⟩ := (shiftFunctor D n).map_surjective (u ≫ (J.commShiftIso n).hom.app E)
    obtain ⟨f,hf⟩ := (h E).2 u₀
    refine ⟨f⟦n⟧', ?_⟩
    apply (cancel_mono ((J.commShiftIso n).hom.app E)).mp
    rw [shifted_comparison J φ E n f, hf]
    exact hu

theorem universal_shifted (h : Universal J φ) (n : ℤ) : Universal J (shifted J φ n) := by
  intro E
  exact target_iso J (shifted J φ n) (shiftNegShift E n)
    (bijective_on_shifted_target J φ h (E⟦-n⟧) n)

variable [HasZeroObject C] [HasZeroObject D]
variable [∀ (n : ℤ), (shiftFunctor C n).Additive]
variable [∀ (n : ℤ), (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]

/-- Strict universal properties on the outer terms imply the middle one. -/
theorem universal_middle {T : Triangle C} {S : Triangle D}
    (ψ : S ⟶ J.mapTriangle.obj T) (hT : T ∈ distTriang C) (hS : S ∈ distTriang D)
    (hA : Universal J ψ.hom₁) (hC : Universal J ψ.hom₃) : Universal J ψ.hom₂ := by
  intro E
  exact middle_bijective J ψ hT hS E (hA E) (hC E)
    (universal_shifted J ψ.hom₁ hA 1 E).2 (universal_shifted J ψ.hom₃ hC (-1) E).1

#print axioms target_iso
#print axioms shifted_comparison
#print axioms bijective_on_shifted_target
#print axioms universal_shifted
#print axioms universal_middle
end Verification.StrictUniversalShift
