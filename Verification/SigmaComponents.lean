/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Sigma Components

Connected components commute with the actual topological disjoint sum.
-/
noncomputable section
namespace Verification.SigmaComponents
variable {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]

def label (x : Σ i, X i) : Σ i, ConnectedComponents (X i) :=
  ⟨x.1,ConnectedComponents.mk x.2⟩

theorem label_continuous : Continuous (label X) :=
  continuous_sigma (fun _ => continuous_sigmaMk.comp ConnectedComponents.continuous_coe)

def components : ConnectedComponents (Σ i, X i) ≃ Σ i, ConnectedComponents (X i) where
  toFun := (label_continuous X).connectedComponentsLift
  invFun x := (continuous_sigmaMk : Continuous (@Sigma.mk ι X x.1)).connectedComponentsMap x.2
  left_inv x := by
    obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe x
    rfl
  right_inv x := by
    rcases x with ⟨i,x⟩
    obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe x
    rfl

#print axioms label
#print axioms label_continuous
#print axioms components
end Verification.SigmaComponents
