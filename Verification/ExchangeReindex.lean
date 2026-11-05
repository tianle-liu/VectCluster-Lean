/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Sum

/-!
# Exchange Reindex

Relabel the mutable vertices and keep every frozen label fixed. These
definitions do not use or preserve any chosen order on the mutable set.
-/
namespace Verification.ExchangeReindex
variable {V W C : Type*} (e : V ≃ W)

def rows : (V ⊕ C) ≃ (W ⊕ C) := Equiv.sumCongr e (Equiv.refl C)

def matrix (B : (W ⊕ C) → W → ℤ) : (V ⊕ C) → V → ℤ :=
  fun a i => B (rows e a) (e i)

theorem rows_inl (v : V) : rows (C := C) e (Sum.inl v) = Sum.inl (e v) := rfl
theorem rows_inr (c : C) : rows (C := C) e (Sum.inr c) = Sum.inr c := rfl
theorem matrix_inl (B : (W ⊕ C) → W → ℤ) (a i : V) :
    matrix e B (Sum.inl a) i = B (Sum.inl (e a)) (e i) := rfl
theorem matrix_inr (B : (W ⊕ C) → W → ℤ) (c : C) (i : V) :
    matrix e B (Sum.inr c) i = B (Sum.inr c) (e i) := rfl

theorem matrix_symm (B : (W ⊕ C) → W → ℤ) : matrix e.symm (matrix e B) = B := by
  funext a i
  cases a <;> simp [matrix, rows]

/-- Order-independent anticlique condition on the principal matrix. -/
def PrincipalIndependent {U : Type*} (B : (U ⊕ C) → U → ℤ) (I : Finset U) : Prop :=
  ∀ a ∈ I, ∀ i ∈ I, a ≠ i → B (Sum.inl a) i = 0

theorem independent_iff (B : (W ⊕ C) → W → ℤ) (I : Finset V) :
    PrincipalIndependent B (I.map e.toEmbedding) ↔ PrincipalIndependent (matrix e B) I := by
  constructor
  · intro h a ha i hi hai
    exact h (e a) (Finset.mem_map.mpr ⟨a,ha,rfl⟩) (e i)
      (Finset.mem_map.mpr ⟨i,hi,rfl⟩) (fun hh => hai (e.injective hh))
  · intro h a ha i hi hai
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hi
    exact h v hv w hw (fun hh => hai (congrArg e hh))

theorem zeroBlock_iff (B : (W ⊕ C) → W → ℤ) (I : Finset V) :
    (∀ a ∈ I.map e.toEmbedding, ∀ i ∈ I.map e.toEmbedding, B (Sum.inl a) i = 0) ↔
      (∀ a ∈ I, ∀ i ∈ I, matrix e B (Sum.inl a) i = 0) := by
  constructor
  · intro h a ha i hi
    exact h (e a) (Finset.mem_map.mpr ⟨a,ha,rfl⟩) (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  · intro h a ha i hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hi
    exact h v hv w hw

#print axioms rows
#print axioms matrix
#print axioms rows_inl
#print axioms rows_inr
#print axioms matrix_inl
#print axioms matrix_inr
#print axioms matrix_symm
#print axioms PrincipalIndependent
#print axioms independent_iff
#print axioms zeroBlock_iff
end Verification.ExchangeReindex
