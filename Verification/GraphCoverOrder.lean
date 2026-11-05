/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverFibers
import Mathlib.Data.Prod.Lex

/-!
# Graph Cover Order

A concrete ordering with cover vertices first, and its exact incidence ranks.
-/

namespace Verification.GraphCoverOrder

open Verification.EvenDifferential

variable {V : Type*} [LinearOrder V]

def CoverOrdered (C : Finset V) : Prop := ∀ i ∈ C, ∀ j ∉ C, i < j

noncomputable def coverOrder (C : Finset V) : LinearOrder V := by
  classical
  let f : V → (Fin 2 ×ₗ V) := fun v => toLex (if v ∈ C then 0 else 1, v)
  exact LinearOrder.lift' f (by intro i j h; exact congrArg (fun x => (ofLex x).2) h)

/-- Every finite cover admits the ordering used in the explicit fiber model. -/
theorem coverOrder_property (C : Finset V) : @CoverOrdered V (coverOrder C) C := by
  intro i hi j hj
  change (toLex ((if i ∈ C then 0 else 1 : Fin 2), i) : Fin 2 ×ₗ V) <
    toLex ((if j ∈ C then 0 else 1 : Fin 2), j)
  rw [Prod.Lex.toLex_lt_toLex]
  left
  simp [hi,hj]

theorem outside_rank (C I K : Finset V) (hC : CoverOrdered C) (hI : I ⊆ C)
    (hK : Disjoint C K) (v : V) (hv : v ∉ C) :
    rankBelow (I ∪ K) v = I.card + rankBelow K v := by
  have hf : I.filter (· < v) = I := Finset.filter_eq_self.mpr (fun i hi => hC i (hI hi) v hv)
  have hd : Disjoint I (K.filter (· < v)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hk
    exact Finset.disjoint_left.mp hK (hI hi) (Finset.mem_filter.mp hk).1
  simp only [rankBelow, Finset.filter_union, hf, Finset.card_union_of_disjoint hd]

theorem inside_rank (C I K : Finset V) (hC : CoverOrdered C)
    (hK : Disjoint C K) (v : V) (hv : v ∈ C) :
    rankBelow (I ∪ K) v = rankBelow I v := by
  have hf : K.filter (· < v) = ∅ := Finset.filter_eq_empty_iff.mpr (by
    intro k hk hkv
    have hkC : k ∉ C := fun hc => Finset.disjoint_left.mp hK hc hk
    exact lt_asymm hkv (hC v hv k hkC))
  simp only [rankBelow, Finset.filter_union, hf, Finset.union_empty]

theorem rank_map_subtype (S : Finset V) (A : Finset {v : V // v ∈ S})
    (a : {v : V // v ∈ S}) :
    rankBelow (A.map (Function.Embedding.subtype _)) a.val = rankBelow A a := by
  simp only [rankBelow, Finset.filter_map, Finset.card_map]
  rfl

#print axioms CoverOrdered
#print axioms coverOrder
#print axioms coverOrder_property
#print axioms outside_rank
#print axioms inside_rank
#print axioms rank_map_subtype

end Verification.GraphCoverOrder
