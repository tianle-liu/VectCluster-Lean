/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingASRows
import Verification.ScalarOpenFreezing

/-!
# Scalar Open Conditions

Actual open freezing retains acyclic order, support and all AS selected
column conditions. The row lattice retains every original coordinate;
removed mutable vertices become frozen coordinates.
-/
noncomputable section
namespace Verification.ScalarOpenConditions
open Verification.IndependentChartIndex Verification.ScalarOpenFreezing
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) {m : ℕ}
variable (h : Selected n I ≃o Fin m)

def retainedVertex (i : Fin m) : Fin n := (h.symm i).val

theorem retainedVertex_injective : Function.Injective (retainedVertex n I h) :=
  Subtype.val_injective.comp h.symm.injective

def originalEquiv : (Fin m ⊕ (Other n I ⊕ κ)) ≃ (Fin n ⊕ κ) :=
  (Equiv.sumCongr h.symm.toEquiv (Equiv.refl _)).trans (originals κ n I).symm

omit [Fintype κ] in
theorem originalEquiv_left (i : Fin m) :
    originalEquiv κ n I h (Sum.inl i) = Sum.inl (retainedVertex n I h i) := rfl

omit [Fintype κ] in
theorem frozenMatrix_eq (r : Fin m ⊕ (Other n I ⊕ κ)) (i : Fin m) :
    frozenMatrix κ n I B m h.toEquiv r (Sum.inl i) =
      B (originalEquiv κ n I h r) (Sum.inl (retainedVertex n I h i)) := rfl

include h in
omit [Fintype κ] in
theorem positive_order
    (hpos : ∀ s i : Fin n, ¬ s < i → (B (Sum.inl s) (Sum.inl i)).toNat = 0) :
    ∀ s i : Fin m, ¬ s < i →
      (frozenMatrix κ n I B m h.toEquiv (Sum.inl s) (Sum.inl i)).toNat = 0 := by
  intro s i hsi
  apply hpos
  intro hh
  exact hsi (h.symm.lt_iff_lt.mp hh)

include h in
omit [Fintype κ] in
theorem negative_order
    (hneg : ∀ s i : Fin n, ¬ i < s → (-B (Sum.inl s) (Sum.inl i)).toNat = 0) :
    ∀ s i : Fin m, ¬ i < s →
      (-frozenMatrix κ n I B m h.toEquiv (Sum.inl s) (Sum.inl i)).toNat = 0 := by
  intro s i his
  apply hneg
  intro hh
  exact his (h.symm.lt_iff_lt.mp hh)

include h in
omit [Fintype κ] in
theorem support
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0) :
    ∀ i j, earlierWeights (Other n I ⊕ κ) m (frozenMatrix κ n I B m h.toEquiv) i j = 0 ↔
      laterWeights (Other n I ⊕ κ) m (frozenMatrix κ n I B m h.toEquiv) i j = 0 := by
  intro i j
  exact hsupport (h.symm i).val (h.symm j).val

omit [Fintype κ] in
theorem adjacent_iff (i j : Fin m) :
    ExchangeRing.Adjacent (laterWeights (Other n I ⊕ κ) m (frozenMatrix κ n I B m h.toEquiv)) i j ↔
      ExchangeRing.Adjacent (laterWeights κ n B) (retainedVertex n I h i) (retainedVertex n I h j) := by
  change (i < j ∧ _ ≠ 0) ∨ (j < i ∧ _ ≠ 0) ↔
    ((h.symm i).val < (h.symm j).val ∧ _ ≠ 0) ∨ ((h.symm j).val < (h.symm i).val ∧ _ ≠ 0)
  rw [show (h.symm i).val < (h.symm j).val ↔ i < j from h.symm.lt_iff_lt]
  rw [show (h.symm j).val < (h.symm i).val ↔ j < i from h.symm.lt_iff_lt]
  rfl

omit [Fintype κ] in
theorem selected_independent (J : Finset (Fin m))
    (hJ : Independent (laterWeights (Other n I ⊕ κ) m (frozenMatrix κ n I B m h.toEquiv)) J) :
    Independent (laterWeights κ n B) (FreezingASRows.selectedOriginal (retainedVertex n I h) J) := by
  classical
  intro w hw z hz
  simp only [FreezingASRows.selectedOriginal, Finset.mem_image] at hw hz
  obtain ⟨i,hi,rfl⟩ := hw
  obtain ⟨j,hj,rfl⟩ := hz
  exact fun hadj => hJ i hi j hj ((adjacent_iff κ n I B h i j).mpr hadj)

theorem allAS
    (hall : ∀ J : Finset (Fin n), Independent (laterWeights κ n B) J →
      AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) J) :
    ∀ J : Finset (Fin m),
      Independent (laterWeights (Other n I ⊕ κ) m (frozenMatrix κ n I B m h.toEquiv)) J →
      AnticliqueSubcolumns.AS (fun q j => frozenMatrix κ n I B m h.toEquiv q (Sum.inl j)) J := by
  intro J hJ
  exact FreezingASRows.AS_transport (retainedVertex n I h) (retainedVertex_injective n I h)
    (originalEquiv κ n I h) (originalEquiv_left κ n I h) (fun q j => B q (Sum.inl j)) J
    (hall _ (selected_independent κ n I B h J hJ))

#print axioms retainedVertex
#print axioms retainedVertex_injective
#print axioms originalEquiv
#print axioms originalEquiv_left
#print axioms frozenMatrix_eq
#print axioms positive_order
#print axioms negative_order
#print axioms support
#print axioms adjacent_iff
#print axioms selected_independent
#print axioms allAS
end Verification.ScalarOpenConditions
