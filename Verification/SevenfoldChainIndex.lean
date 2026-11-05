/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldGraphFreeness
import Verification.GraphChainMatrix

/-!
# Sevenfold Chain Index

An explicit enumeration of the actual sevenfold independence simplices.
The induced subsets retain their genuine simplex support condition.
-/
noncomputable section
open scoped Classical
namespace Verification.SevenfoldChainIndex
open Verification.SevenfoldGraphFreeness Verification.GraphCover

def face : Fin 10 → Finset (Fin 5) :=
  ![∅,{0},{1},{2},{3},{4},{0,2},{1,2},{1,3},{0,3}]

theorem injective : Function.Injective face := by decide

theorem independent_iff : ∀ I : Finset (Fin 5),
    graph.IsIndepSet (I : Set (Fin 5)) ↔ ∃ i : Fin 10,face i=I := by
  unfold SimpleGraph.IsIndepSet Set.Pairwise
  unfold graph OriginalEvenWittGraph.graph OriginalMutableGraph.graph
  decide

def index (T : Finset (Fin 5)) : {i : Fin 10 // face i ⊆ T} ≃ Simplex graph T :=
  Equiv.ofBijective (fun i => ⟨face i.val,i.property,(independent_iff _).mpr ⟨i.val,rfl⟩⟩) (by
    constructor
    · intro i j h
      apply Subtype.ext
      exact injective (congrArg Subtype.val h)
    · intro J
      obtain ⟨i,hi⟩ := (independent_iff J.val).mp J.property.2
      exact ⟨⟨i,hi.symm ▸ J.property.1⟩,Subtype.ext hi⟩)

theorem index_face (T : Finset (Fin 5)) (i : {i : Fin 10 // face i ⊆ T}) :
    (index T i).val = face i.val := rfl

#print axioms face
#print axioms injective
#print axioms independent_iff
#print axioms index
#print axioms index_face
end Verification.SevenfoldChainIndex
