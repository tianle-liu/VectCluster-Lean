/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Fin.Basic

/-!
# Normal Frame Insertion

The actual permutation from the newly added normal parameter followed
by the old increasing frame to the new increasing frame. Its determinant
sign is the parity of the number of old parameters below the new one.
-/
namespace Verification.NormalFrameInsertion
open Finset
variable {V : Type*} [LinearOrder V] [DecidableEq V]
variable (I : Finset V) (j : V) (hj : j ∉ I)

noncomputable def newFrame : Fin (I.card + 1) ↪o V :=
  (insert j I).orderEmbOfFin (card_insert_of_not_mem hj)

noncomputable def position : Fin (I.card + 1) :=
  ((insert j I).orderIsoOfFin (card_insert_of_not_mem hj)).symm ⟨j, mem_insert_self _ _⟩

theorem newFrame_position : newFrame I j hj (position I j hj) = j := by
  exact congrArg Subtype.val
    (((insert j I).orderIsoOfFin (card_insert_of_not_mem hj)).apply_symm_apply
      ⟨j, mem_insert_self _ _⟩)

theorem below_image : (Iio (position I j hj)).image (newFrame I j hj) =
    I.filter (fun i => i < j) := by
  ext v
  constructor
  · rintro hv
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hv
    have hlt : newFrame I j hj q < j := by
      exact ((newFrame I j hj).strictMono (mem_Iio.mp hq)).trans_eq
        (newFrame_position I j hj)
    refine mem_filter.mpr ⟨?_, hlt⟩
    have hm := (insert j I).orderEmbOfFin_mem (card_insert_of_not_mem hj) q
    exact (mem_insert.mp hm).resolve_left (ne_of_lt hlt)
  · intro hv
    obtain ⟨hv,hlt⟩ := mem_filter.mp hv
    let q := ((insert j I).orderIsoOfFin (card_insert_of_not_mem hj)).symm
      ⟨v, mem_insert_of_mem hv⟩
    have heq : newFrame I j hj q = v :=
      congrArg Subtype.val (((insert j I).orderIsoOfFin (card_insert_of_not_mem hj)).apply_symm_apply _)
    refine mem_image.mpr ⟨q, mem_Iio.mpr ?_, heq⟩
    apply (newFrame I j hj).lt_iff_lt.mp
    rw [heq, newFrame_position]
    exact hlt

theorem position_val : (position I j hj).val = (I.filter (fun i => i < j)).card := by
  rw [← below_image I j hj, card_image_of_injective _ (newFrame I j hj).injective]
  exact (Fin.card_Iio _).symm

theorem oldFrame (q : Fin I.card) :
    newFrame I j hj ((position I j hj).succAbove q) = I.orderEmbOfFin rfl q := by
  have h := Finset.orderEmbOfFin_unique (s := I) rfl
    (f := fun q : Fin I.card => newFrame I j hj ((position I j hj).succAbove q))
    (fun q => by
      have hm := (insert j I).orderEmbOfFin_mem (card_insert_of_not_mem hj)
        ((position I j hj).succAbove q)
      apply (mem_insert.mp hm).resolve_left
      intro he
      have hn := he.trans (newFrame_position I j hj).symm
      exact (position I j hj).succAbove_ne q ((newFrame I j hj).injective hn))
    ((newFrame I j hj).strictMono.comp (Fin.strictMono_succAbove _))
  exact congrFun h q

noncomputable def permutation : Equiv.Perm (Fin (I.card + 1)) :=
  (position I j hj).cycleRange

theorem frame_reordering :
    Fin.cons j (I.orderEmbOfFin rfl) ∘ permutation I j hj = newFrame I j hj := by
  funext q
  refine Fin.succAboveCases (position I j hj) ?_ (fun k => ?_) q
  · simp [permutation, newFrame_position]
  · simp [permutation, oldFrame]

theorem permutation_sign : Equiv.Perm.sign (permutation I j hj) =
    (-1) ^ (I.filter (fun i => i < j)).card := by
  rw [permutation, Fin.sign_cycleRange, position_val]

theorem orientation_factor {M : Type*} [Monoid M] (orientation : ℤˣ →* M) :
    orientation (Equiv.Perm.sign (permutation I j hj)) =
      orientation (-1) ^ (I.filter (fun i => i < j)).card := by
  rw [permutation_sign, map_pow]

#print axioms newFrame
#print axioms position
#print axioms newFrame_position
#print axioms below_image
#print axioms position_val
#print axioms oldFrame
#print axioms permutation
#print axioms frame_reordering
#print axioms permutation_sign
#print axioms orientation_factor
end Verification.NormalFrameInsertion
