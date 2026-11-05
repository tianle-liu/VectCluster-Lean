/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ResidualReindexAS

/-!
# Residual Reindex Conditions

Increasing mutable reindexing preserves acyclic order and graph
independence; the original AS condition supplies the AS condition of the
new actual scalar seed.
-/
noncomputable section
namespace Verification.ResidualReindexConditions
open Verification.ResidualScalarReentry Verification.ResidualReindexAS
open Verification.FreezingIndex Verification.ActualScalarFreezing
open Verification.ActualResidualColumns Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)
variable {m r : ℕ} (h : Remaining κ n B v ≃o Fin m)
variable (e : QuotientLattice κ n B v ≃ₗ[ℤ] (Fin r →₀ ℤ))

include h e in
theorem positive_order
    (hpos : ∀ s i : Fin n, ¬ s < i → (B (Sum.inl s) (Sum.inl i)).toNat = 0) :
    ∀ s i : Fin m, ¬ s < i →
      (reindexedMatrix κ n B v h.toEquiv e (Sum.inl s) (Sum.inl i)).toNat = 0 := by
  intro s i hsi
  apply hpos
  intro hh
  exact hsi (h.symm.lt_iff_lt.mp hh)

include h e in
theorem negative_order
    (hneg : ∀ s i : Fin n, ¬ i < s → (-B (Sum.inl s) (Sum.inl i)).toNat = 0) :
    ∀ s i : Fin m, ¬ i < s →
      (-reindexedMatrix κ n B v h.toEquiv e (Sum.inl s) (Sum.inl i)).toNat = 0 := by
  intro s i his
  apply hneg
  intro hh
  exact his (h.symm.lt_iff_lt.mp hh)

include h e in
theorem support
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0) :
    ∀ i j, earlierWeights (Fin r) m (reindexedMatrix κ n B v h.toEquiv e) i j = 0 ↔
      laterWeights (Fin r) m (reindexedMatrix κ n B v h.toEquiv e) i j = 0 := by
  intro i j
  exact hsupport (h.symm i).val (h.symm j).val

theorem adjacent_iff (i j : Fin m) :
    ExchangeRing.Adjacent (laterWeights (Fin r) m (reindexedMatrix κ n B v h.toEquiv e)) i j ↔
      ExchangeRing.Adjacent (laterWeights κ n B) (h.symm i).val (h.symm j).val := by
  change (i < j ∧ _ ≠ 0) ∨ (j < i ∧ _ ≠ 0) ↔
    ((h.symm i).val < (h.symm j).val ∧ _ ≠ 0) ∨ ((h.symm j).val < (h.symm i).val ∧ _ ≠ 0)
  rw [show (h.symm i).val < (h.symm j).val ↔ i < j from h.symm.lt_iff_lt]
  rw [show (h.symm j).val < (h.symm i).val ↔ j < i from h.symm.lt_iff_lt]
  rfl

omit e [Fintype κ] in
theorem selected_remaining (I : Finset (Fin m)) (w : Fin n)
    (hw : w ∈ selectedOriginal κ n B v h.toEquiv I) :
    w ≠ v ∧ ¬ ExchangeRing.Adjacent (laterWeights κ n B) v w := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
  exact (h.symm i).property

theorem selected_independent (I : Finset (Fin m))
    (hI : Independent (laterWeights (Fin r) m (reindexedMatrix κ n B v h.toEquiv e)) I) :
    Independent (laterWeights κ n B) (selectedOriginal κ n B v h.toEquiv I) := by
  intro w hw z hz
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
  exact fun hadj => hI i hi j hj ((adjacent_iff κ n B v h e i j).mpr hadj)

theorem allAS
    (hpos : ∀ s i : Fin n, ¬ s < i → (B (Sum.inl s) (Sum.inl i)).toNat = 0)
    (hneg : ∀ s i : Fin n, ¬ i < s → (-B (Sum.inl s) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I) :
    ∀ I : Finset (Fin m),
      Independent (laterWeights (Fin r) m (reindexedMatrix κ n B v h.toEquiv e)) I →
      AnticliqueSubcolumns.AS (fun q j => reindexedMatrix κ n B v h.toEquiv e q (Sum.inl j)) I := by
  intro I hI
  apply AS_transport κ n B v h.toEquiv e I
  apply residual_AS_of_allAS κ n B v (selectedOriginal κ n B v h.toEquiv I)
    (fun hv => (selected_remaining κ n B v h I v hv).1 rfl)
    (fun w hw => (selected_remaining κ n B v h I w hw).2)
    hpos hneg hsupport hall
  exact selected_independent κ n B v h e I hI

#print axioms positive_order
#print axioms negative_order
#print axioms support
#print axioms adjacent_iff
#print axioms selected_remaining
#print axioms selected_independent
#print axioms allAS
end Verification.ResidualReindexConditions
