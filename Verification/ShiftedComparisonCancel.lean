/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictUniversalShift

/-!
# Shifted Comparison Cancel

Shift cancellation for actual cross-category comparison maps. The
formula uses the commutation coherence of the functor, not faithfulness.
-/
noncomputable section
namespace Verification.ShiftedComparisonCancel
open CategoryTheory CategoryTheory.Limits
open Verification.StrictTriangleHom
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
variable {X : D} {P : C} (φ : X ⟶ F.obj P)

omit [Preadditive C] [Preadditive D] [F.Additive] in
theorem cancel : shifted F (shifted F φ (-1)) 1 ≫ F.map (shiftNegShift P (1 : ℤ)).hom =
    (shiftNegShift X (1 : ℤ)).hom ≫ φ := by
  dsimp only [shifted,shiftNegShift,shiftEquiv,shiftEquiv']
  simp only [Iso.app_hom]
  rw [Functor.map_shiftFunctorCompIsoId_hom_app]
  simp only [Functor.map_comp,Category.assoc,Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp_assoc,Category.assoc,Iso.inv_hom_id_app,Category.comp_id,Functor.map_id,Category.id_comp]
  simpa only [Functor.comp_obj,Category.comp_id,Functor.comp_map,Functor.id_map] using
    (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by omega)).hom.naturality φ

#print axioms cancel
end Verification.ShiftedComparisonCancel
