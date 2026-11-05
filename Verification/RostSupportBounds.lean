/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostSupportInput
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Rost Support Bounds

The coordinate support row has its literal independence-height
bound. This is a consequence of its indexing set, not an extra bound
on the cohomology supplied by the support-sequence input.
-/
noncomputable section
namespace Verification.RostSupportBounds
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (T : RostAffineInput.Theory)
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop) (s : ℤ)
variable (D : RostSupportInput.Data T A V x Allowed s)

theorem layer_above (p q : ℕ) (hp : PrimeIndependentHeight.height V Allowed < p) :
    IsZero (RostSupportInput.Layer T A V x Allowed s p q) := by
  letI : IsEmpty (PrimeLayerCover.Index Allowed p) := ⟨fun I => by
    have h := PrimeIndependentHeight.card_le_height V Allowed I.val I.property.2
    rw [I.property.1] at h
    omega⟩
  exact AddCommGrp.isZero_of_subsingleton _

theorem row_above (p : ℕ) (hp : PrimeIndependentHeight.height V Allowed < p) :
    IsZero (D.row.X p) :=
  IsZero.of_iso (layer_above T A V x Allowed s p 0 hp) (D.rowTerm p)

theorem row_homology_above (p : ℕ) (hp : PrimeIndependentHeight.height V Allowed < p) :
    IsZero (D.row.homology p) :=
  (D.row.sc p).isZero_homology_of_isZero_X₂ (row_above T A V x Allowed s D p hp)

include D in
theorem cohomology_above
    (hrow : ∀ p q,q≠0 → IsZero (D.pages.E 1 p q))
    (p : ℕ) (hp : PrimeIndependentHeight.height V Allowed < p) :
    IsZero ((T.cycles (Spec (CommRingCat.of A)) s).homology p) :=
  IsZero.of_iso (row_homology_above T A V x Allowed s D p hp)
    (OneRowConvergence.cohomologyIso D.convergence hrow D.row D.rowHomology p)

#print axioms layer_above
#print axioms row_above
#print axioms row_homology_above
#print axioms cohomology_above
end Verification.RostSupportBounds
