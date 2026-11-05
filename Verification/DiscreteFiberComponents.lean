/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Data.Finite.Card

/-!
# Discrete Fiber Components

Identification of actual connected components from a continuous label
map with nonempty connected fibers. Used for the real sign decomposition.
-/
noncomputable section
namespace Verification.DiscreteFiberComponents
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TotallyDisconnectedSpace Y]
variable (f : X → Y) (hf : Continuous f)
  (hconn : ∀ y : Y, PreconnectedSpace {x : X // f x=y})

include hconn in
theorem lift_injective : Function.Injective hf.connectedComponentsLift := by
  intro a b hab
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨y,rfl⟩ := ConnectedComponents.surjective_coe b
  apply ConnectedComponents.coe_eq_coe'.mpr
  have hs : IsPreconnected {z : X | f z=f y} := isPreconnected_iff_preconnectedSpace.mpr (hconn (f y))
  exact hs.subset_connectedComponent rfl hab

theorem lift_surjective (hsur : Function.Surjective f) : Function.Surjective hf.connectedComponentsLift := by
  intro y
  obtain ⟨x,hx⟩ := hsur y
  exact ⟨ConnectedComponents.mk x,hx⟩

def componentsEquiv (hsur : Function.Surjective f) : ConnectedComponents X ≃ Y :=
  Equiv.ofBijective hf.connectedComponentsLift
    ⟨lift_injective f hf hconn,lift_surjective f hf hsur⟩

include hf hconn in
theorem card_components (hsur : Function.Surjective f) :
    Nat.card (ConnectedComponents X)=Nat.card Y := Nat.card_congr (componentsEquiv f hf hconn hsur)

#print axioms lift_injective
#print axioms lift_surjective
#print axioms componentsEquiv
#print axioms card_components
end Verification.DiscreteFiberComponents
