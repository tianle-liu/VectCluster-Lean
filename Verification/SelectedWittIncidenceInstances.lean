/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SelectedWittIncidenceSign

/-!
# Selected Witt Incidence Instances

The original incidence sign is independent of the equality-decision
instance used to erase the selected normal coordinate.
-/
noncomputable section
namespace Verification.SelectedWittIncidenceInstances
variable {V : Type*} [LinearOrder V] (J : Finset V) (v : J)

theorem sign (d : DecidableEq J) :
    ((-1 : ℤ)^((@Finset.erase J d Finset.univ v).filter (fun i : J => i<v)).card) =
      Verification.SubsetProjectionComplex.sign J v.val := by
  have hd : d=(fun a b : J => Subtype.instDecidableEq a b) := Subsingleton.elim _ _
  rw [hd]
  exact SelectedWittIncidenceSign.sign J v

#print axioms sign
end Verification.SelectedWittIncidenceInstances
