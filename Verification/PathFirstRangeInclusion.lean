/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualKillRelations

/-!
# Path First Range Inclusion

One inclusion of the literal first-boundary image comparison follows
from the explicit unit pivots for every original relation generator.
-/

namespace Verification.PathFirstRangeInclusion

open Verification.PathFirstBoundary Verification.PathSignNormalization
  Verification.PathFirstBoundaryCutout Verification.PathActualSlideRelations Verification.PathActualKillRelations

variable {R : Type*} [CommRing R]

theorem z_signed_range_le (g : R) (hg : g*g=1) (n : ℕ) :
    LinearMap.range (signedBoundary g false (n+1)) ≤ LinearMap.range (zBoundary g n) := by
  rw [signedBoundary,Finsupp.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  cases j with
  | inl w => exact z_killed_boundary g hg n w.val w.property
  | inr uv => exact z_slide_boundary g hg n uv.val.1 uv.val.2 uv.property

theorem y_signed_range_le (g : R) (hg : g*g=1) (a : ℕ) :
    LinearMap.range (signedBoundary g true (2*a)) ≤ LinearMap.range (yBoundary g a) := by
  rw [signedBoundary,Finsupp.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  cases j with
  | inl w => exact y_killed_boundary g hg a w.val w.property
  | inr uv => exact y_slide_boundary g hg a uv.val.1 uv.val.2 uv.property

#print axioms z_signed_range_le
#print axioms y_signed_range_le

end Verification.PathFirstRangeInclusion
