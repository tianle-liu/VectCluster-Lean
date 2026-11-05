/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldExchangeMatrix
import Verification.Sevenfold
import Verification.PrimeIndependentHeight

/-!
# Sevenfold Actual Independent Sets

Identify the actual exchange-matrix independent sets with the existing
kernel-checked sevenfold mask computation; the graph homology is not redone.
-/
namespace Verification.SevenfoldActualIndependentSets
open Verification.SevenfoldExchangeMatrix Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover

def vertices (t : Fin 32) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => Verification.Sevenfold.contains t.val i.val = true)

theorem color_agrees : ∀ i : Fin 5, (color i).val = Verification.Sevenfold.color i.val := by decide

theorem independent_iff : ∀ t : Fin 32,
    Independent (laterWeights (Fin 2) 5 matrix) (vertices t) ↔
      Verification.Sevenfold.independent t.val = true := by
  unfold Independent Verification.ExchangeRing.Adjacent
  decide

theorem card_agrees : ∀ t : Fin 32, (vertices t).card = Verification.Sevenfold.size t.val := by decide

theorem all_sets_represented : ∀ I : Finset (Fin 5), ∃ t : Fin 32, vertices t = I := by decide

theorem independent_card_le_two (I : Finset (Fin 5))
    (hI : Independent (laterWeights (Fin 2) 5 matrix) I) : I.card ≤ 2 := by
  obtain ⟨t, rfl⟩ := all_sets_represented I
  rw [card_agrees]
  exact Verification.Sevenfold.no_independent_triples t ((independent_iff t).mp hI)

theorem independent_pair :
    Independent (laterWeights (Fin 2) 5 matrix) ({0, 2} : Finset (Fin 5)) ∧
      ({0, 2} : Finset (Fin 5)).card = 2 := by
  unfold Independent Verification.ExchangeRing.Adjacent
  decide

theorem height_eq_two : Verification.PrimeIndependentHeight.height (Fin 5)
    (Independent (laterWeights (Fin 2) 5 matrix)) = 2 := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro I hI
    exact independent_card_le_two I (Finset.mem_filter.mp hI).2
  · have h := Verification.PrimeIndependentHeight.card_le_height (Fin 5)
      (Independent (laterWeights (Fin 2) 5 matrix)) ({0, 2} : Finset (Fin 5)) independent_pair.1
    rw [independent_pair.2] at h
    exact h

#print axioms vertices
#print axioms color_agrees
#print axioms independent_iff
#print axioms card_agrees
#print axioms all_sets_represented
#print axioms independent_card_le_two
#print axioms independent_pair
#print axioms height_eq_two
end Verification.SevenfoldActualIndependentSets
