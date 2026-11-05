/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AllowedComponentRow

/-!
# Allowed Predecessor Sum

Reindex a support-row sum by the missing vertex of each incident
predecessor. No component or cohomology compatibility is assumed here.
-/
noncomputable section
namespace Verification.AllowedPredecessorSum
open scoped BigOperators
open Verification.AllowedComponentRow
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Allowed : Finset α → Prop)
variable (hereditary : ∀ J, Allowed J → ∀ v : J, Allowed (J.erase v.val))
variable (p : ℕ) (J : Target Allowed p)

omit [Fintype α] in
theorem predecessor_injective : Function.Injective (predecessor Allowed hereditary p J) := by
  intro v w h
  apply Subtype.ext
  by_contra hne
  have hmem : v.val ∈ J.val.erase w.val := Finset.mem_erase.mpr ⟨hne,v.property⟩
  have hs : J.val.erase v.val = J.val.erase w.val := congrArg Subtype.val h
  rw [← hs] at hmem
  exact Finset.not_mem_erase _ _ hmem

omit [Fintype α] in
theorem exists_predecessor (I : Source Allowed p) (hIJ : I.val ⊆ J.val) :
    ∃ v : J.val, predecessor Allowed hereditary p J v = I := by
  classical
  have hex : ∃ v ∈ J.val, v ∉ I.val := by
    by_contra h
    have hsub : J.val ⊆ I.val := by
      intro v hv
      by_contra hi
      exact h ⟨v,hv,hi⟩
    have hc := Finset.card_le_card hsub
    have hi := I.property.1
    have hj := J.property.1
    omega
  obtain ⟨v,hv,hi⟩ := hex
  refine ⟨⟨v,hv⟩, Subtype.ext ?_⟩
  change J.val.erase v = I.val
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    exact Finset.mem_erase.mpr ⟨fun hav => hi (hav ▸ ha),hIJ ha⟩
  · rw [Finset.card_erase_of_mem hv,J.property.1,I.property.1]
    omega

variable {G : Type*} [AddCommMonoid G]

theorem sum (f : Source Allowed p → G)
    (hzero : ∀ I : Source Allowed p, ¬ I.val ⊆ J.val → f I = 0) :
    letI : Fintype (Source Allowed p) := Fintype.ofFinite _
    ∑ I : Source Allowed p, f I = ∑ v : J.val, f (predecessor Allowed hereditary p J v) := by
  classical
  letI : Fintype (Source Allowed p) := Fintype.ofFinite _
  have himage : Finset.univ.image (predecessor Allowed hereditary p J) =
      Finset.univ.filter (fun I : Source Allowed p => I.val ⊆ J.val) := by
    ext I
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨v,rfl⟩
      exact Finset.erase_subset v.val J.val
    · exact exists_predecessor Allowed hereditary p J I
  calc
    ∑ I : Source Allowed p, f I =
        ∑ I ∈ Finset.univ.filter (fun I : Source Allowed p => I.val ⊆ J.val), f I := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro I _ hI
      apply hzero I
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hI
    _ = ∑ I ∈ Finset.univ.image (predecessor Allowed hereditary p J), f I := by rw [himage]
    _ = ∑ v : J.val, f (predecessor Allowed hereditary p J v) := by
      rw [Finset.sum_image (fun a _ b _ h => predecessor_injective Allowed hereditary p J h)]

#print axioms predecessor_injective
#print axioms exists_predecessor
#print axioms sum
end Verification.AllowedPredecessorSum
