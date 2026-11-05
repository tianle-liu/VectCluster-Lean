/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingOrder

/-!
# Freezing Order Equiv

Relabeling the actual ordering condition transports its full principal
submatrices, not merely its support graph.
-/
namespace Verification.FreezingOrderEquiv
variable (C : ∀ n : ℕ,(Fin n→Fin n→ℤ)→Prop)
variable {α β : Type} (A : α→α→ℤ) (E : α→α→Prop) (rank : α→ℕ)

theorem pullback (h : FreezingOrder.Good C A E rank) (f : β≃α) :
    FreezingOrder.Good C (fun i j=>A (f i) (f j)) (fun i j=>E (f i) (f j)) (rank ∘ f) := by
  intro v m g hg
  apply h (f v) m (g.trans f.toEmbedding)
  intro w
  obtain ⟨z,rfl⟩ := f.surjective w
  constructor
  · rintro ⟨i,hi⟩
    have hh : z∈Set.range g := ⟨i,f.injective hi⟩
    exact (hg z).mp hh
  · intro hz
    obtain ⟨i,hi⟩ := (hg z).mpr hz
    exact ⟨i,congrArg f hi⟩

theorem transport (f : α≃β) (B : β→β→ℤ) (F : β→β→Prop)
    (hA : ∀ i j,B (f i) (f j)=A i j)
    (hr : Function.Injective rank)
    (h : FreezingOrder.Good C A (fun i j=>F (f i) (f j)) rank) :
    ∃r : β→ℕ,Function.Injective r ∧ FreezingOrder.Good C B F r := by
  refine ⟨rank ∘ f.symm,hr.comp f.symm.injective,?_⟩
  have hp := pullback C A (fun i j=>F (f i) (f j)) rank h f.symm
  have hh : (fun i j=>A (f.symm i) (f.symm j))=B := by
    funext i j
    simpa only [Equiv.apply_symm_apply] using (hA (f.symm i) (f.symm j)).symm
  simpa only [hh,Equiv.apply_symm_apply] using hp

#print axioms pullback
#print axioms transport
end Verification.FreezingOrderEquiv
