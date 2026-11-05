/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverCoordinates
import Verification.GraphCoverOrder
import Verification.GraphSimplexChains

/-!
# Graph Cover Coordinate Facts

Coordinate identities for graph-cover fibers, including the cover and outside
parts, cardinalities, deletion of outside vertices, and their order ranks.
-/

namespace Verification.GraphCoverCoordinateFacts

open Verification.GraphCover Verification.GraphCoverFibers
  Verification.GraphCoverCoordinates Verification.GraphCoverOrder
  Verification.GraphSimplexChains Verification.EvenDifferential

variable {V : Type*} [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V) (hC : Covers G C)

theorem fiberIndex_val (I : CoverSimplex G C T) (A : Finset (RemainingVertex G C T I)) :
    (fiberIndexEquiv G C T hC ⟨I,A⟩).val =
      I.val ∪ A.map (Function.Embedding.subtype _) := rfl

theorem mapped_outside (I : CoverSimplex G C T) (A : Finset (RemainingVertex G C T I)) :
    Disjoint C (A.map (Function.Embedding.subtype _)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hm
  have hvR := Finset.property_of_mem_map_subtype _ hm
  exact ((mem_remaining G C T I.val v).mp hvR).2.1 hv

theorem fiberIndex_cover (I : CoverSimplex G C T) (A : Finset (RemainingVertex G C T I)) :
    (fiberIndexEquiv G C T hC ⟨I,A⟩).val ∩ C = I.val :=
  fiber_cover_part G C T I (subtypeFinsetEquiv (remaining G C T I.val) A)

theorem fiberIndex_outside (I : CoverSimplex G C T) (A : Finset (RemainingVertex G C T I)) :
    (fiberIndexEquiv G C T hC ⟨I,A⟩).val \ C = A.map (Function.Embedding.subtype _) :=
  fiber_outside_part G C T I (subtypeFinsetEquiv (remaining G C T I.val) A)

theorem fiberIndex_card (I : CoverSimplex G C T) (A : Finset (RemainingVertex G C T I)) :
    (fiberIndexEquiv G C T hC ⟨I,A⟩).val.card = I.val.card + A.card := by
  rw [fiberIndex_val, Finset.card_union_of_disjoint]
  · rw [Finset.card_map]
  · exact (mapped_outside G C T I A).mono_left (by
      intro v hv; exact (Finset.mem_inter.mp (I.property.1 hv)).2)

theorem fiberIndex_erase_outside (I : CoverSimplex G C T)
    (A : Finset (RemainingVertex G C T I)) (a : RemainingVertex G C T I) :
    eraseSimplex G T (fiberIndexEquiv G C T hC ⟨I,A⟩) a.val =
      fiberIndexEquiv G C T hC ⟨I,A.erase a⟩ := by
  apply Subtype.ext
  change (I.val ∪ A.map (Function.Embedding.subtype _)).erase a.val =
    I.val ∪ (A.erase a).map (Function.Embedding.subtype _)
  have haI : a.val ∉ I.val := by
    intro hi
    exact ((mem_remaining G C T I.val a.val).mp a.property).2.1
      (Finset.mem_inter.mp (I.property.1 hi)).2
  rw [Finset.erase_union_distrib, Finset.erase_eq_of_not_mem haI, Finset.map_erase]
  rfl

theorem fiberIndex_outside_rank (hord : CoverOrdered C) (I : CoverSimplex G C T)
    (A : Finset (RemainingVertex G C T I)) (a : RemainingVertex G C T I) :
    rankBelow (fiberIndexEquiv G C T hC ⟨I,A⟩).val a.val =
      I.val.card + rankBelow A a := by
  rw [fiberIndex_val, outside_rank C I.val _ hord
    (fun v hv => (Finset.mem_inter.mp (I.property.1 hv)).2)
    (mapped_outside G C T I A) a.val ((mem_remaining G C T I.val a.val).mp a.property).2.1,
    rank_map_subtype]

#print axioms fiberIndex_val
#print axioms mapped_outside
#print axioms fiberIndex_cover
#print axioms fiberIndex_outside
#print axioms fiberIndex_card
#print axioms fiberIndex_erase_outside
#print axioms fiberIndex_outside_rank

end Verification.GraphCoverCoordinateFacts
