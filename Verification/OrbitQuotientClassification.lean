/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Orbit Quotient Classification

A surjective classifier whose fibers modulo isomorphism are exactly
group orbits induces an actual quotient equivalence, including injectivity.
-/
noncomputable section
namespace Verification.OrbitQuotientClassification
variable {A H G : Type*} [Group G] [MulAction G H]
variable (S : Setoid A) (f : A → H)
variable (hf : Function.Surjective f)
variable (hrel : ∀ a b,S a b ↔ MulAction.orbitRel G H (f a) (f b))

def map : Quotient S → Quotient (MulAction.orbitRel G H) :=
  Quotient.map f (fun a b hab => (hrel a b).mp hab)

include hf in
theorem map_surjective : Function.Surjective (map S f hrel) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro h
  obtain ⟨a,rfl⟩ := hf h
  exact ⟨Quotient.mk S a,rfl⟩

theorem map_injective : Function.Injective (map S f hrel) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y hxy
  exact Quotient.sound ((hrel x y).mpr (Quotient.exact hxy))

def equiv : Quotient S ≃ Quotient (MulAction.orbitRel G H) :=
  Equiv.ofBijective (map S f hrel) ⟨map_injective S f hrel,map_surjective S f hf hrel⟩

#print axioms map
#print axioms map_surjective
#print axioms map_injective
#print axioms equiv
end Verification.OrbitQuotientClassification
