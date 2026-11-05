/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Module Additive Iso

Preserve the additive group of a module-category isomorphism while
using its canonical integer scalar action.
-/
noncomputable section
namespace Verification.ModuleAdditiveIso
open CategoryTheory

def additive {X Y : ModuleCat ℤ} (e : X ≅ Y) : X ≃+ Y where
  toFun := fun z => e.hom z
  invFun := fun z => e.inv z
  left_inv z := congrArg (fun f : X ⟶ X => f z) e.hom_inv_id
  right_inv z := congrArg (fun f : Y ⟶ Y => f z) e.inv_hom_id
  map_add' x y := map_add e.hom.hom x y

def linear {X Y : ModuleCat ℤ} (e : X ≅ Y) : X ≃ₗ[ℤ] Y := (additive e).toIntLinearEquiv

#print axioms additive
#print axioms linear
end Verification.ModuleAdditiveIso
