/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.CategoryTheory.EqToHom

/-!
# Equality Conjugation

Cancellation of equality transports, without an isomorphism-instance search.
-/
namespace Verification.EqualityConjugation
open CategoryTheory
variable {C : Type*} [Category C]
theorem cancel {W X Y Z : C} (hX : W=X) (hY : Y=Z) (f g : X⟶Y)
    (h : eqToHom hX ≫ f ≫ eqToHom hY=eqToHom hX ≫ g ≫ eqToHom hY) : f=g := by
  subst W
  subst Z
  simpa only [eqToHom_refl,Category.id_comp,Category.comp_id] using h
#print axioms cancel
end Verification.EqualityConjugation
