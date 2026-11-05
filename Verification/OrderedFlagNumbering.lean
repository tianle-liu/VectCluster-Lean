/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedThomSections
import Verification.OrderedFlagThomAction

/-!
# Ordered Flag Numbering

The increasing frame used in the actual flag comparison is the
canonical Fin numbering used in every coefficient term.
-/
noncomputable section
namespace Verification.OrderedFlagNumbering
open Verification.OrderedFlagNormalCoordinates
variable (ι : Type) [Fintype ι] [LinearOrder ι] (v : ι)

theorem card_count : Fintype.card ι = count ι v := by
  exact (Finset.card_erase_add_one (Finset.mem_univ v)).symm

theorem increasing_numbering : increasing ι v =
    OrderedThomSections.numbering ι (count ι v) (card_count ι v) := by
  apply Equiv.ext
  have h := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset ι))
    (card_count ι v) (f := increasing ι v) (fun _ => Finset.mem_univ _)
    (NormalFrameInsertion.newFrame (oldSet ι v) v (by simp [oldSet])).strictMono
  exact congrFun h

#print axioms card_count
#print axioms increasing_numbering
end Verification.OrderedFlagNumbering
