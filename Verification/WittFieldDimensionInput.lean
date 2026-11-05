/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WittSheafSectionsInput
import Mathlib.Data.ZMod.Basic

/-!
# Witt Field Dimension Input

The ordinary dimension-modulo-two invariant of the Witt ring of a
field. This field input supplies a nonvanishing witness, with no variety
or cohomology among its assumptions.
-/
noncomputable section
namespace Verification.WittFieldDimensionInput
open CategoryTheory AlgebraicGeometry
variable (k : Type) [Field k] (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})

structure Standard where
  dimension : WittSheafSectionsInput.RingSection W k →+ ZMod 2
  dimension_one : dimension 1=1

variable (H : Standard k W)
include H in
theorem nontrivial : Nontrivial (WittSheafSectionsInput.RingSection W k) := by
  refine ⟨⟨0,1,?_⟩⟩
  intro h
  have hh := congrArg H.dimension h
  rw [map_zero,H.dimension_one] at hh
  exact zero_ne_one hh

#print axioms Standard
#print axioms nontrivial
end Verification.WittFieldDimensionInput
