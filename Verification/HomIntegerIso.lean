/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Hom Integer Iso

Actual precomposition along an object isomorphism, as a linear
isomorphism of the canonical integer modules on morphism groups.
-/
namespace Verification.HomIntegerIso
open CategoryTheory
variable {C : Type*} [Category C] [Preadditive C]

def precompose {X Y : C} (e : X ≅ Y) (M : C) : (X ⟶ M) ≃ₗ[ℤ] (Y ⟶ M) :=
  AddEquiv.toIntLinearEquiv {
    toFun := fun f => e.inv ≫ f
    invFun := fun f => e.hom ≫ f
    left_inv := fun f => by simp only [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
    right_inv := fun f => by simp only [← Category.assoc,Iso.inv_hom_id,Category.id_comp]
    map_add' := fun f g => by simp only [Preadditive.comp_add] }

#print axioms precompose
end Verification.HomIntegerIso
