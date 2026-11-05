/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.CategoryTheory.Iso

/-!
# Composed Frame Differential

A differential comparison in intermediate frames gives the commutative square for the composed frames.
-/
namespace Verification.ComposedFrameDifferential
open CategoryTheory
variable {C : Type*} [Category C] {X Y X' Y' X'' Y'' : C}

theorem comm (e : X ≅ X') (f : Y ≅ Y') (a : X' ≅ X'') (b : Y' ≅ Y'')
    (d : X ⟶ Y) (d' : X'' ⟶ Y'')
    (h : e.inv ≫ d ≫ f.hom=a.hom ≫ d' ≫ b.inv) :
    d ≫ (f ≪≫ b).hom=(e ≪≫ a).hom ≫ d' := by
  apply (cancel_epi e.inv).1
  apply (cancel_mono b.inv).1
  simpa only [Iso.trans_hom,Category.assoc,Iso.inv_hom_id_assoc,Iso.hom_inv_id,Category.comp_id] using h

#print axioms comm
end Verification.ComposedFrameDifferential
