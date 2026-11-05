/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCover
import Mathlib.Data.Finset.Max

/-!
# Graph Balanced Cover

A maximum independent subset produces a cover whose surviving simplices
have at most half the vertices. This supplies the manuscript's 2p vertex
bound through the explicit graph-cover chain contraction.
-/

namespace Verification.GraphBalancedCover

open Classical Verification.GraphCover

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V)

/-- Maximum, not merely maximal, independence inside the specified induced graph. -/
def MaximumIndependent (S : Finset V) : Prop :=
  S ⊆ T ∧ G.IsIndepSet (S : Set V) ∧
    ∀ J : Finset V, J ⊆ T → G.IsIndepSet (J : Set V) → J.card ≤ S.card

omit [Fintype V] in
theorem maximumIndependent_exists : ∃ S, MaximumIndependent G T S := by
  let sets := T.powerset.filter (fun S : Finset V => G.IsIndepSet (S : Set V))
  have hn : sets.Nonempty := by
    refine ⟨∅,?_⟩
    simp [sets, SimpleGraph.IsIndepSet]
  obtain ⟨S,hS,hmax⟩ := Finset.exists_max_image sets Finset.card hn
  have hm := Finset.mem_filter.mp hS
  refine ⟨S,Finset.mem_powerset.mp hm.1,hm.2,?_⟩
  intro J hJT hJ
  exact hmax J (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hJT,hJ⟩)

noncomputable def maximumSet : Finset V := Classical.choose (maximumIndependent_exists G T)

omit [Fintype V] in
theorem maximumSet_spec : MaximumIndependent G T (maximumSet G T) :=
  Classical.choose_spec (maximumIndependent_exists G T)

/-- Taking the complement in the whole vertex type gives a cover of the whole graph. -/
noncomputable def balancedCover : Finset V := Finset.univ \ maximumSet G T

theorem balancedCover_covers : Covers G (balancedCover G T) := by
  intro u v huv
  by_cases hu : u ∈ maximumSet G T
  · right
    have hv : v ∉ maximumSet G T := by
      intro h
      exact independent_not_adj G (maximumSet_spec G T).2.1 hu h huv
    simp [balancedCover, hv]
  · left; simp [balancedCover, hu]

theorem survivor_twice_card (J : Simplex G T)
    (hJ : Survives G (balancedCover G T) T J) : 2 * J.val.card ≤ T.card := by
  have hmax := (maximumSet_spec G T).2.2 J.val J.property.1 J.property.2
  have hd : Disjoint J.val (maximumSet G T) := by
    apply Finset.disjoint_left.mpr
    intro v hv hs
    exact (Finset.mem_sdiff.mp (hJ.1 hv)).2 hs
  have hu : J.val ∪ maximumSet G T ⊆ T :=
    Finset.union_subset J.property.1 (maximumSet_spec G T).1
  have hc := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

#print axioms MaximumIndependent
#print axioms maximumIndependent_exists
#print axioms maximumSet
#print axioms maximumSet_spec
#print axioms balancedCover
#print axioms balancedCover_covers
#print axioms survivor_twice_card

end Verification.GraphBalancedCover
