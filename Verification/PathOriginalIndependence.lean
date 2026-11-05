/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalYStratum
import Verification.PathOriginalZStratum

/-!
# Path Original Independence

The literal Y/Z matrices satisfy the ordering and independent-set
hypotheses of the general geometric row, with the original vertex numbering.
-/
namespace Verification.PathOriginalIndependence
open Verification.PathCompression Verification.PathOriginalStratumTransport
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable {κ : Type} {n : ℕ}
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hB : ∀ a i : Fin n, B (Sum.inl a) (Sum.inl i)=PathLattice.pathMatrix n a i)

include hB in
theorem positive_order (a i : Fin n) (ha : ¬ a < i) : (B (Sum.inl a) (Sum.inl i)).toNat=0 := by
  rw [hB,PathLattice.pathMatrix]
  have h : ¬ i.val=a.val+1 := by intro hh;apply ha;exact Fin.lt_def.mpr (by omega)
  simp only [if_neg h,zero_sub]
  split <;> norm_num

include hB in
theorem negative_order (a i : Fin n) (ha : ¬ i < a) : (-B (Sum.inl a) (Sum.inl i)).toNat=0 := by
  rw [hB,PathLattice.pathMatrix]
  have h : ¬ a.val=i.val+1 := by intro hh;apply ha;exact Fin.lt_def.mpr (by omega)
  simp only [if_neg h,sub_zero]
  split <;> norm_num

include hB in
theorem support (i j : Fin n) : earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0 := by
  have he : earlierWeights κ n B i j=laterWeights κ n B i j := by
    unfold earlierWeights laterWeights
    rw [hB,hB]
    congr 1
    unfold PathLattice.pathMatrix
    ring
  rw [he]

include hB in
theorem independent {I : Finset ℕ} (hI : Admissible n I) :
    Independent (laterWeights κ n B) (mutableSet n I) := by
  intro i hi j hj
  have hi' := (mem_mutableSet n I i).mp hi
  have hj' := (mem_mutableSet n I j).mp hj
  have hn₁ : ¬ i.val=j.val+1 := by
    intro h
    exact hI.2 (j.val+1) hj' (by simpa only [h] using hi')
  have hn₂ : ¬ j.val=i.val+1 := by
    intro h
    exact hI.2 (i.val+1) hi' (by simpa only [h] using hj')
  simp [ExchangeRing.Adjacent,laterWeights,hB,PathLattice.pathMatrix,hn₁,hn₂]

theorem y_mutable (a i : Fin n) : PathOriginalYPresentation.matrix n (Sum.inl a) (Sum.inl i)=
    PathLattice.pathMatrix n a i := rfl

theorem z_mutable (a i : Fin n) : PathOriginalZPresentation.matrix n (Sum.inl a) (Sum.inl i)=
    PathLattice.pathMatrix n a i := rfl

#print axioms positive_order
#print axioms negative_order
#print axioms support
#print axioms independent
#print axioms y_mutable
#print axioms z_mutable
end Verification.PathOriginalIndependence
