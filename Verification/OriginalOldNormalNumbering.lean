/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AdjacentCoordinatePair
import Verification.OrderedThomSections

/-!
# Original Old Normal Numbering

Deleting one normal coordinate preserves the increasing order of
all surviving original coordinates. Hence the actual old-index map
commutes with canonical Fin numberings without a permutation factor.
-/
noncomputable section
namespace Verification.OriginalOldNormalNumbering
open Verification.IndependentChartIndex
variable (n : ℕ) (J : Finset (Fin n)) (v : Selected n J)

def orderIso : CoordinateFlag.Old (Selected n J) v ≃o Selected n (J.erase v.val) where
  toEquiv := AdjacentCoordinatePair.indexEquiv n J v
  map_rel_iff' := Iff.rfl

theorem strictMono : StrictMono (AdjacentCoordinatePair.indexEquiv n J v) :=
  (orderIso n J v).strictMono

theorem numbering (r : ℕ) (hs : Fintype.card (CoordinateFlag.Old (Selected n J) v) = r)
    (ht : Fintype.card (Selected n (J.erase v.val)) = r) (i : Fin r) :
    AdjacentCoordinatePair.indexEquiv n J v
      (OrderedThomSections.numbering (CoordinateFlag.Old (Selected n J) v) r hs i) =
    OrderedThomSections.numbering (Selected n (J.erase v.val)) r ht i := by
  have h := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Selected n (J.erase v.val))))
    ht (f := fun k => AdjacentCoordinatePair.indexEquiv n J v
      (OrderedThomSections.numbering (CoordinateFlag.Old (Selected n J) v) r hs k))
    (fun _ => Finset.mem_univ _)
    ((strictMono n J v).comp (Fintype.orderIsoFinOfCardEq _ hs).strictMono)
  exact congrFun h i

#print axioms orderIso
#print axioms strictMono
#print axioms numbering
end Verification.OriginalOldNormalNumbering
