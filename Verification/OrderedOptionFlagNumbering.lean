/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedFlagNumbering
import Mathlib.Order.WithBot

/-!
# Ordered Option Flag Numbering

The standard none-first order used for a new normal direction agrees
with the actual flag's new-first normal numbering.
-/
noncomputable section
namespace Verification.OrderedOptionFlagNumbering
open Verification.OrderedFlagNormalCoordinates
variable (ι : Type) [Fintype ι] [LinearOrder ι] (v : ι)

local instance optionOrder : LinearOrder (Option (CoordinateFlag.Old ι v)) :=
  inferInstanceAs (LinearOrder (WithBot (CoordinateFlag.Old ι v)))

theorem card_count : Fintype.card (FlagNormalCoordinates.Normals ι v)=count ι v := by
  exact (Fintype.card_congr (normalOrder ι v)).symm.trans (Fintype.card_fin _)

theorem normalOrder_strictMono : StrictMono (normalOrder ι v) := by
  intro a
  refine Fin.cases ?_ (fun a => ?_) a
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · intro hab
      exact False.elim (lt_irrefl _ hab)
    · intro _
      rw [normalOrder_new,normalOrder_old]
      exact WithBot.bot_lt_coe _
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · intro hab
      exact False.elim (not_lt_of_ge (Fin.zero_le _) hab)
    · intro hab
      rw [normalOrder_old,normalOrder_old]
      exact WithBot.coe_lt_coe.mpr ((oldSet ι v).orderEmbOfFin rfl |>.strictMono
        (Fin.succ_lt_succ_iff.mp hab))

theorem normalOrder_numbering : normalOrder ι v =
    OrderedThomSections.numbering (FlagNormalCoordinates.Normals ι v)
      (count ι v) (card_count ι v) := by
  apply Equiv.ext
  have h := Finset.orderEmbOfFin_unique
    (s := (Finset.univ : Finset (FlagNormalCoordinates.Normals ι v)))
    (card_count ι v) (f := normalOrder ι v) (fun _ => Finset.mem_univ _)
    (normalOrder_strictMono ι v)
  exact congrFun h

#print axioms optionOrder
#print axioms card_count
#print axioms normalOrder_strictMono
#print axioms normalOrder_numbering
end Verification.OrderedOptionFlagNumbering
