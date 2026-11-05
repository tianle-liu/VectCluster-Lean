/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostSupportBounds
import Verification.RostMilnorInput

/-!
# Rost Row Truncation

In weight p the support row has no terms in degree greater than p.
In particular the last outgoing differential is zero. This follows from
ordinary negative Milnor weights, not from a target Chow formula.
-/
noncomputable section
namespace Verification.RostRowTruncation
open CategoryTheory CategoryTheory.Limits
variable (T : RostAffineInput.Theory) (N : RostMilnorInput.NegativeWeights T)
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop) (p : ℕ)
variable (D : RostSupportInput.Data T A V x Allowed p)

include N in
theorem layer_above (r : ℕ) (hr : p<r) :
    IsZero (RostSupportInput.Layer T A V x Allowed p r 0) := by
  have hz (I : Verification.PrimeLayerCover.Index Allowed r) :=
    N.zero (AlgebraicGeometry.Spec (CommRingCat.of (Verification.PrimeStratumPresentation.ClosedRing x I.val)))
      ((p : ℤ)-r) (by omega)
  letI : Subsingleton (RostSupportInput.Layer T A V x Allowed p r 0) :=
    ⟨fun a b => by
      funext I
      exact congrArg (fun f => f (a I)) ((hz I).eq_of_src (𝟙 _) 0) |>.trans
        (congrArg (fun f => f (b I)) ((hz I).eq_of_src (𝟙 _) 0)).symm⟩
  exact AddCommGrp.isZero_of_subsingleton _

include N in
theorem row_above (r : ℕ) (hr : p<r) : IsZero (D.row.X r) :=
  IsZero.of_iso (layer_above T N A V x Allowed p r hr) (D.rowTerm r)

include N in
theorem outgoing_zero : D.row.d p (p+1)=0 :=
  (row_above T N A V x Allowed p D (p+1) (Nat.lt_succ_self p)).eq_of_tgt _ _

#print axioms layer_above
#print axioms row_above
#print axioms outgoing_zero
end Verification.RostRowTruncation
