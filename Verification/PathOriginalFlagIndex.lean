/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalConfigurationIndex
import Verification.PathOriginalFaceIndex
import Verification.OriginalTotalOrderedRow

/-!
# Path Original Flag Index

Typed adjacent flags of the actual path filtration, with the literal
path codimension and the original selected normal vertex.
-/
noncomputable section
namespace Verification.PathOriginalFlagIndex
open Finset Verification.PathCompression Verification.PathCochains
open Verification.PathOriginalStratumTransport Verification.PathOriginalFaceIndex
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable {κ : Type} [Fintype κ] {n : ℕ}
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hB : ∀ a i : Fin n,B (Sum.inl a) (Sum.inl i)=PathLattice.pathMatrix n a i)
variable {I : Finset ℕ} (hI : Admissible n I)
variable (j : ℕ) (hj : j∈Icc 1 n) (ha : Addable I j)

include hI hB in
omit [Fintype κ] in
theorem mutable_card : (mutableSet n I).card=I.card :=
  PathOriginalConfigurationIndex.config_card B hB ⟨I,hI⟩

def target : ActualCellThom.Index κ n B (I.card+1) :=
  ⟨mutableSet n (insert j I),by
    have ha' : j∉I := fun h => ha.1 (mem_union_left _ h)
    rw [mutable_card B hB (PathSignedFaceUnits.nextAdmissible hI j hj ha),card_insert_of_not_mem ha'],
    PathOriginalIndependence.independent B hB (PathSignedFaceUnits.nextAdmissible hI j hj ha)⟩

omit [Fintype κ] in
theorem edge_val :
    (ActualGlobalBoundary.edgeIndex κ n B I.card (target B hB hI j hj ha)
      (selectedNormal (I:=I) j hj)).val=mutableSet n I := mutable_erase j hj ha

omit [Fintype κ] in
theorem preceding :
    (((univ.erase (selectedNormal (I:=I) j hj)).filter
      (fun i : IndependentChartIndex.Selected n (target B hB hI j hj ha).val =>
        i<selectedNormal j hj))).card=PathRhoConfiguration.rank I j :=
  preceding_count j hj hI

#print axioms mutable_card
#print axioms target
#print axioms edge_val
#print axioms preceding
end Verification.PathOriginalFlagIndex
