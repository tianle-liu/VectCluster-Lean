/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalEvenWittGraph
import Verification.SevenfoldActualIndependentSets
import Verification.GraphCoverTheorem

/-!
# Sevenfold Graph Freeness

The literal sevenfold graph satisfies the all-induced integral
homology freeness hypothesis, by the proved general graph-cover theorem.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.SevenfoldGraphFreeness
open Verification.SevenfoldExchangeMatrix Verification.GraphCover

def graph : SimpleGraph (Fin 5) := OriginalEvenWittGraph.graph (Fin 2) 5 matrix

theorem independent_card (I : Finset (Fin 5)) (hI : graph.IsIndepSet (I : Set (Fin 5))) :
    I.card ≤ 2 :=
  SevenfoldActualIndependentSets.independent_card_le_two I
    ((OriginalEvenWittGraph.independent_iff (Fin 2) 5 matrix positive_order negative_order support I).mpr hI)

theorem covers : Covers graph Finset.univ := by
  intro u v _
  exact Or.inl (Finset.mem_univ u)

theorem cover_rank : coverRank graph Finset.univ ≤ 2 := by
  apply Finset.sup_le
  intro I hI
  exact independent_card I (Finset.mem_filter.mp hI).2

theorem chain_free : GraphChainTF.ChainGraphFree graph := by
  have hc : @coverRank (Fin 5) (fun a b => LinearOrder.toDecidableEq a b) graph Finset.univ ≤ 2 := by
    rw [GraphCoverTheorem.coverRank_decidable graph Finset.univ
      (fun a b => LinearOrder.toDecidableEq a b) (instDecidableEqFin 5)]
    exact cover_rank
  exact GraphCoverTheorem.small_cover_chainGraphFree graph Finset.univ covers hc

#print axioms graph
#print axioms independent_card
#print axioms covers
#print axioms cover_rank
#print axioms chain_free
end Verification.SevenfoldGraphFreeness
