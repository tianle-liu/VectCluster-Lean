/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Module Homology Zero Incoming

A short complex with zero incoming object has its genuine categorical
homology canonically identified with the kernel of its outgoing map.
-/
noncomputable section
namespace Verification.ModuleHomologyZeroIncoming
open CategoryTheory
variable {R : Type*} [CommRing R] (S : ShortComplex (ModuleCat R))
attribute [local instance 2000] ModuleCat.isModule

theorem range_zero [Subsingleton S.X₁] : LinearMap.range S.moduleCatToCycles=⊥ := by
  rw [LinearMap.range_eq_bot]
  ext x
  rw [Subsingleton.elim x 0,map_zero]
  rfl

def equiv [Subsingleton S.X₁] : S.homology ≃ₗ[R] LinearMap.ker S.g.hom :=
  S.moduleCatHomologyIso.toLinearEquiv.trans
    ((LinearMap.range S.moduleCatToCycles).quotEquivOfEqBot (range_zero S))

#print axioms range_zero
#print axioms equiv
end Verification.ModuleHomologyZeroIncoming
