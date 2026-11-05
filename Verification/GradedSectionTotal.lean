/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.DirectSum.Basic

/-!
# Graded Section Total

Additive totalization of an ordinary graded section ring. The direct-sum
identification records the usual meaning of a graded ring; all total maps
and uniqueness statements below are constructed from individual degrees.
-/
noncomputable section
namespace Verification.GradedSectionTotal
open scoped DirectSum
variable {H K : ℤ → Type*} [∀ q, AddCommGroup (H q)] [∀ q, AddCommGroup (K q)]
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable (E : (⨁ q, H q) ≃+ A) (F : (⨁ q, K q) ≃+ B)

def includeDegree (q : ℤ) : H q →+ A := E.toAddMonoidHom.comp (DirectSum.of H q)

theorem includeDegree_injective (q : ℤ) : Function.Injective (includeDegree E q) :=
  E.injective.comp (DirectSum.of_injective q)

def reindexMap (δ : ℤ → ℤ) (m : ∀ q,H q →+ K (δ q)) : A →+ B :=
  (DirectSum.toAddMonoid (fun q => (includeDegree F (δ q)).comp (m q))).comp E.symm.toAddMonoidHom

theorem reindexMap_degree (δ : ℤ → ℤ) (m : ∀ q,H q →+ K (δ q)) (q : ℤ) (a : H q) :
    reindexMap E F δ m (includeDegree E q a) = includeDegree F (δ q) (m q a) := by
  simp only [reindexMap,includeDegree,AddMonoidHom.comp_apply,AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe,AddEquiv.symm_apply_apply,DirectSum.toAddMonoid_of]

theorem hom_ext {C : Type*} [AddCommGroup C] (f g : A →+ C)
    (h : ∀ q a,f (includeDegree E q a)=g (includeDegree E q a)) : f=g := by
  have he : f.comp E.toAddMonoidHom = g.comp E.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    exact h
  apply AddMonoidHom.ext
  intro a
  obtain ⟨x,rfl⟩ := E.surjective a
  exact DFunLike.congr_fun he x

#print axioms includeDegree
#print axioms includeDegree_injective
#print axioms reindexMap
#print axioms reindexMap_degree
#print axioms hom_ext
end Verification.GradedSectionTotal
