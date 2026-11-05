/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphBlocks
import Mathlib.Data.Fintype.EquivFin

/-!
# Graph Block Multiplicity

Counting the actual fiber of `(S,F) ↦ S ∖ c⁻¹(F)`.
The multiplicity is derived from the literal block index, not imposed as
an independent formula for the graph complex.
-/
noncomputable section
open scoped Classical
namespace Verification.GraphBlockMultiplicity
open Verification.GraphBlocks
variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]
variable (c : V → C)

def missing (T : Finset V) : Finset C := Finset.univ \ T.image c

def Fiber (T : Finset V) :=
  {SF : Finset V × Finset C // available c SF.1 SF.2 = T}

def Extra (T : Finset V) :=
  (F : ↥((missing c T).powerset)) × ↥((colorPreimage c F.val).powerset)

def fiberFintype (T : Finset V) : Fintype (Fiber c T) :=
  inferInstanceAs (Fintype {SF : Finset V × Finset C // available c SF.1 SF.2 = T})
attribute [instance] fiberFintype

def extraFintype (T : Finset V) : Fintype (Extra c T) :=
  inferInstanceAs (Fintype ((F : ↥((missing c T).powerset)) × ↥((colorPreimage c F.val).powerset)))
attribute [instance] extraFintype

omit [Fintype V] [DecidableEq V] in
theorem disjoint_iff (T : Finset V) (F : Finset C) :
    Disjoint (T.image c) F ↔ F ⊆ missing c T := by
  constructor
  · intro h a ha
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun ht => Finset.disjoint_left.mp h ht ha⟩
  · intro h
    exact Finset.disjoint_left.mpr fun a ha hf => (Finset.mem_sdiff.mp (h hf)).2 ha

omit [Fintype V] [Fintype C] [DecidableEq V] in
theorem available_disjoint (S : Finset V) (F : Finset C) :
    Disjoint ((available c S F).image c) F := by
  apply Finset.disjoint_left.mpr
  rintro a ha hf
  rcases Finset.mem_image.mp ha with ⟨i,hi,rfl⟩
  exact (Finset.mem_filter.mp hi).2 hf

def fiberExtraEquiv (T : Finset V) : Fiber c T ≃ Extra c T where
  toFun SF := ⟨⟨SF.val.2, Finset.mem_powerset.mpr ((disjoint_iff c T SF.val.2).mp
    (by simpa only [SF.property] using available_disjoint c SF.val.1 SF.val.2))⟩,
    ⟨SF.val.1 ∩ colorPreimage c SF.val.2, Finset.mem_powerset.mpr Finset.inter_subset_right⟩⟩
  invFun E := ⟨(T ∪ E.2.val,E.1.val), available_union_extra T E.2.val E.1.val
    ((disjoint_iff c T E.1.val).mpr (Finset.mem_powerset.mp E.1.property))
    (Finset.mem_powerset.mp E.2.property)⟩
  left_inv SF := by
    apply Subtype.ext
    exact Prod.ext (recover_block_set SF.val.1 T SF.val.2 SF.property) rfl
  right_inv E := by
    rcases E with ⟨F,A⟩
    change (⟨F,⟨(T ∪ A.val) ∩ colorPreimage c F.val,_⟩⟩ : Extra c T) = ⟨F,A⟩
    congr 1
    apply Subtype.ext
    exact congrArg (fun s : {S : Finset V // S ⊆ colorPreimage c F.val} => s.val) ((fixedFrozenEquiv T F.val
      ((disjoint_iff c T F.val).mpr (Finset.mem_powerset.mp F.property))).right_inv
      ⟨A.val,Finset.mem_powerset.mp A.property⟩)

def multiplicity (T : Finset V) : ℕ :=
  ∏ a ∈ missing c T, (1 + 2 ^ (Finset.univ.filter fun i : V => c i = a).card)

theorem fiber_card (T : Finset V) : Fintype.card (Fiber c T) = multiplicity c T := by
  rw [Fintype.card_congr (fiberExtraEquiv c T)]
  simp only [Extra,Fintype.card_sigma,Fintype.card_coe,Finset.card_powerset]
  exact (Finset.sum_coe_sort (missing c T).powerset
    (fun F => 2 ^ (colorPreimage c F).card)).trans (multiplicity_product c (missing c T))

def fiberFinEquiv (T : Finset V) : Fiber c T ≃ Fin (multiplicity c T) :=
  (Fintype.equivFin (Fiber c T)).trans (finCongr (fiber_card c T))

omit [Fintype C] [DecidableEq C] in
theorem principal (T : Finset V) :
    multiplicity (fun i : V => i) T = 3 ^ (Fintype.card V - T.card) := by
  simpa only [multiplicity,missing,Finset.image_id'] using principal_coefficient_weight T

#print axioms principal
#print axioms missing
#print axioms Fiber
#print axioms Extra
#print axioms fiberFintype
#print axioms extraFintype
#print axioms disjoint_iff
#print axioms available_disjoint
#print axioms fiberExtraEquiv
#print axioms multiplicity
#print axioms fiber_card
#print axioms fiberFinEquiv
end Verification.GraphBlockMultiplicity
