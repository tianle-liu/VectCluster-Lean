/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenWittPfisterBasis
import Verification.FinsetSubtypeCoordinates
import Mathlib.Data.Finset.Sum

/-!
# Even Witt Word Index

The literal remaining-coordinate Pfister basis is indexed by exactly
the disjoint mutable/frozen subset pairs used in the graph decomposition.
-/
noncomputable section
open scoped Classical
namespace Verification.EvenWittWordIndex
variable {V C : Type*} (c : V → C) (I : Finset V)

abbrev LocalIndex := {AF : Finset V × Finset C // Disjoint I AF.1 ∧ Disjoint (I.image c) AF.2}

theorem range_mutable (v : V) :
    Sum.inl v ∈ Set.range (EvenWittCoordinateSplit.selected c I) ↔ v ∈ I := by
  constructor
  · rintro ⟨a,ha⟩
    cases a with
    | inl a => exact (Sum.inl.inj ha) ▸ a.property
    | inr a => cases ha
  · intro hv
    exact ⟨Sum.inl ⟨v,hv⟩,rfl⟩

theorem range_frozen (a : C) :
    Sum.inr a ∈ Set.range (EvenWittCoordinateSplit.selected c I) ↔ a ∈ I.image c := by
  constructor
  · rintro ⟨v,hv⟩
    cases v with
    | inl v => cases hv
    | inr v => exact Finset.mem_image.mpr ⟨v.val,v.property,Sum.inr.inj hv⟩
  · intro ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨Sum.inr ⟨v,hv⟩,rfl⟩

theorem predicate (K : Finset (V ⊕ C)) :
    (∀ a ∈ K, a ∉ Set.range (EvenWittCoordinateSplit.selected c I)) ↔
      Disjoint I K.toLeft ∧ Disjoint (I.image c) K.toRight := by
  constructor
  · intro h
    constructor
    · apply Finset.disjoint_left.mpr
      intro v hv hK
      exact h (Sum.inl v) (Finset.mem_toLeft.mp hK) ((range_mutable c I v).mpr hv)
    · apply Finset.disjoint_left.mpr
      intro a ha hK
      exact h (Sum.inr a) (Finset.mem_toRight.mp hK) ((range_frozen c I a).mpr ha)
  · rintro ⟨hV,hC⟩ a ha hs
    cases a with
    | inl v => exact Finset.disjoint_left.mp hV ((range_mutable c I v).mp hs) (Finset.mem_toLeft.mpr ha)
    | inr a => exact Finset.disjoint_left.mp hC ((range_frozen c I a).mp hs) (Finset.mem_toRight.mpr ha)

def equiv : Finset (EvenWittPfisterBasis.Remaining c I) ≃ LocalIndex c I :=
  (FinsetSubtypeCoordinates.equiv (fun a => a ∉ Set.range (EvenWittCoordinateSplit.selected c I))).trans
    (Finset.sumEquiv.toEquiv.subtypeEquiv (predicate c I))

theorem equiv_val (A : Finset (EvenWittPfisterBasis.Remaining c I)) :
    (equiv c I A).val =
      ((A.map (Function.Embedding.subtype _)).toLeft,(A.map (Function.Embedding.subtype _)).toRight) := rfl

#print axioms LocalIndex
#print axioms range_mutable
#print axioms range_frozen
#print axioms predicate
#print axioms equiv
#print axioms equiv_val
end Verification.EvenWittWordIndex
