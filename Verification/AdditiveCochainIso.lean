/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Additive Cochain Iso

A degreewise additive equivalence commuting with all adjacent maps is
an isomorphism of the actual integer-module cochain complexes.
-/
noncomputable section
namespace Verification.AdditiveCochainIso
open CategoryTheory
attribute [local instance 2000] ModuleCat.isModule
def linear {X Y : ModuleCat.{0} ℤ} (e : X ≃+ Y) : X →ₗ[ℤ] Y where
  toFun := e
  map_add' := e.map_add
  map_smul' r x := by
    change e (@SMul.smul ℤ X X.isModule.toSMul r x) = @SMul.smul ℤ Y Y.isModule.toSMul r (e x)
    rw [int_smul_eq_zsmul,int_smul_eq_zsmul]
    exact map_zsmul e r x

def component {X Y : ModuleCat.{0} ℤ} (e : X ≃+ Y) : X ≅ Y where
  hom := ModuleCat.ofHom (linear e)
  inv := ModuleCat.ofHom (linear e.symm)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply x

variable (C D : CochainComplex (ModuleCat.{0} ℤ) ℕ)
variable (e : ∀ p, C.X p ≃+ D.X p)
variable (h : ∀ p x, D.d p (p+1) (e p x)=e (p+1) (C.d p (p+1) x))

def iso : C ≅ D :=
  HomologicalComplex.Hom.isoOfComponents (fun p => component (e p)) (by
    intro p q hpq
    have hq : p+1=q := hpq
    subst q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact h p x)

#print axioms linear
#print axioms component
#print axioms iso
end Verification.AdditiveCochainIso
