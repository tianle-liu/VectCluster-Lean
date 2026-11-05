/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DiscreteFiberComponents
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homotopy.Contractible

/-!
# Component Homeomorph

Connected component spaces under a homeomorphism, and the actual
component subspace identified with a connected fiber of a discrete label.
-/
noncomputable section
namespace Verification.ComponentHomeomorph
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def components (e : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv x := by
    obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe x
    change ConnectedComponents.mk (e.symm (e x))=ConnectedComponents.mk x
    rw [e.symm_apply_apply]
  right_inv y := by
    obtain ⟨y,rfl⟩ := ConnectedComponents.surjective_coe y
    change ConnectedComponents.mk (e (e.symm y))=ConnectedComponents.mk y
    rw [e.apply_symm_apply]

variable [TotallyDisconnectedSpace Y]

theorem component_eq_fiber (f : X → Y) (hf : Continuous f)
    (hconn : ∀ y : Y, PreconnectedSpace {x : X // f x=y}) (x : X) :
    connectedComponent x={y : X | f y=f x} := by
  ext y
  constructor
  · intro hy
    have hh := ConnectedComponents.coe_eq_coe'.mpr hy
    exact congrArg hf.connectedComponentsLift hh
  · intro hy
    exact ConnectedComponents.coe_eq_coe'.mp
      (DiscreteFiberComponents.lift_injective f hf hconn hy)

def fiber (f : X → Y) (hf : Continuous f)
    (hconn : ∀ y : Y, PreconnectedSpace {x : X // f x=y}) (x : X) :
    connectedComponent x ≃ₜ {y : X // f y=f x} :=
  Homeomorph.setCongr (component_eq_fiber f hf hconn x)

theorem component_contractible (f : X → Y) (hf : Continuous f)
    (hcontr : ∀ y : Y, ContractibleSpace {x : X // f x=y}) (x : X) :
    ContractibleSpace (connectedComponent x) := by
  have hc : ∀ y : Y, PreconnectedSpace {x : X // f x=y} := by
    intro y
    letI := hcontr y
    infer_instance
  letI := hcontr (f x)
  exact (fiber f hf hc x).contractibleSpace

#print axioms components
#print axioms component_eq_fiber
#print axioms fiber
#print axioms component_contractible
end Verification.ComponentHomeomorph
