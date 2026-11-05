/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.Localization.Basic

/-!
# Nested Localization

Inverting a smaller collection first does not change the localization
at a larger collection. Both directions are the actual universal maps.
-/
noncomputable section
namespace Verification.NestedLocalization
variable {A : Type*} [CommRing A] (M N : Submonoid A) (h : M ≤ N)

abbrev Iterated := Localization (N.map (algebraMap A (Localization M)))

def firstMap : Localization M →ₐ[A] Localization N :=
  IsLocalization.liftAlgHom (M := M) (f := Algebra.ofId A (Localization N))
    (fun m => IsLocalization.map_units (Localization N) (⟨(m : A), h m.2⟩ : N))

def forward : Iterated M N →ₐ[A] Localization N :=
  IsLocalization.liftAlgHom (M := N.map (algebraMap A (Localization M)))
    (f := firstMap M N h) (by
      rintro ⟨_, a, ha, rfl⟩
      rw [AlgHom.commutes]
      exact IsLocalization.map_units (Localization N) ⟨a, ha⟩)

def backward : Localization N →ₐ[A] Iterated M N :=
  IsLocalization.liftAlgHom (M := N) (f := Algebra.ofId A (Iterated M N)) (by
    intro n
    change IsUnit (algebraMap A (Iterated M N) (n : A))
    rw [IsScalarTower.algebraMap_apply A (Localization M) (Iterated M N)]
    exact IsLocalization.map_units (Iterated M N)
      (⟨algebraMap A (Localization M) (n : A), (n : A), n.2, rfl⟩ :
        N.map (algebraMap A (Localization M))))

theorem backward_forward : (backward M N).comp (forward M N h) = AlgHom.id A _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (N.map (algebraMap A (Localization M)))
  apply IsLocalization.ringHom_ext M
  apply RingHom.ext
  intro a
  change backward M N (forward M N h
    (algebraMap (Localization M) (Iterated M N) (algebraMap A (Localization M) a))) = _
  rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes, AlgHom.commutes]
  rfl

theorem forward_backward : (forward M N h).comp (backward M N) = AlgHom.id A _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext N
  apply RingHom.ext
  intro a
  change forward M N h (backward M N (algebraMap A (Localization N) a)) =
    algebraMap A (Localization N) a
  rw [AlgHom.commutes, AlgHom.commutes]

def equiv : Iterated M N ≃ₐ[A] Localization N :=
  AlgEquiv.ofAlgHom (forward M N h) (backward M N)
    (forward_backward M N h) (backward_forward M N h)

#print axioms Iterated
#print axioms firstMap
#print axioms forward
#print axioms backward
#print axioms backward_forward
#print axioms forward_backward
#print axioms equiv
end Verification.NestedLocalization
