/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Order

/-!
# Freezing Order

The ordering condition in the freezing argument, with its actual
later nonneighbor sets. Restriction removes the least vertex in this
ordering; no closure hypothesis on the matrix class is used.
-/
namespace Verification.FreezingOrder
variable (C : ∀ n : ℕ, (Fin n → Fin n → ℤ) → Prop)
variable {α β : Type} (A : α → α → ℤ) (E : α → α → Prop) (rank : α → ℕ)

def Good : Prop := ∀ (v : α) (m : ℕ) (g : Fin m ↪ α),
  (∀ w, w ∈ Set.range g ↔ rank v < rank w ∧ ¬ E v w) →
  C m (fun i j => A (g i) (g j))

include C in
theorem at_minimum (h : Good C A E rank) (hinj : Function.Injective rank)
    (v : α) (hmin : ∀ w, rank v ≤ rank w) (m : ℕ) (g : Fin m ↪ α)
    (hg : ∀ w, w ∈ Set.range g ↔ w ≠ v ∧ ¬ E v w) :
    C m (fun i j => A (g i) (g j)) := by
  apply h v m g
  intro w
  rw [hg]
  constructor
  · rintro ⟨hne,he⟩
    exact ⟨lt_of_le_of_ne (hmin w) (fun hh => hne (hinj hh.symm)),he⟩
  · rintro ⟨hlt,he⟩
    exact ⟨fun hh => by subst w; exact (lt_irrefl _ hlt),he⟩

include C in
theorem restrict (h : Good C A E rank) (v : α) (hmin : ∀ w, rank v ≤ rank w)
    (f : β ↪ α) (hf : ∀ w, w ∈ Set.range f ↔ w ≠ v)
    (A' : β → β → ℤ) (E' : β → β → Prop)
    (hA : ∀ i j, A' i j = A (f i) (f j))
    (hE : ∀ i j, E' i j ↔ E (f i) (f j)) :
    Good C A' E' (rank ∘ f) := by
  intro u m g hg
  have hh : ∀ w, w ∈ Set.range (g.trans f) ↔ rank (f u) < rank w ∧ ¬ E (f u) w := by
    intro w
    constructor
    · rintro ⟨i,rfl⟩
      have hi := (hg (g i)).mp ⟨i,rfl⟩
      exact ⟨hi.1, fun he => hi.2 ((hE u (g i)).mpr he)⟩
    · rintro ⟨hlt,he⟩
      have hne : w ≠ v := by
        intro hh
        subst w
        exact (not_lt_of_ge (hmin (f u))) hlt
      obtain ⟨z,rfl⟩ := (hf w).mpr hne
      have hz : z ∈ Set.range g := (hg z).mpr ⟨hlt,fun hz => he ((hE u z).mp hz)⟩
      obtain ⟨i,rfl⟩ := hz
      exact ⟨i,rfl⟩
  simpa only [Function.Embedding.trans_apply,← hA] using h (f u) m (g.trans f) hh

variable [Fintype α] [Nonempty α]
theorem exists_minimum : ∃ v : α, ∀ w, rank v ≤ rank w := by
  obtain ⟨v,_,hv⟩ := Finset.exists_min_image Finset.univ rank Finset.univ_nonempty
  exact ⟨v,fun w => hv w (Finset.mem_univ w)⟩

#print axioms Good
#print axioms at_minimum
#print axioms restrict
#print axioms exists_minimum
end Verification.FreezingOrder
