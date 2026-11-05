/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenAcyclicCover
import Verification.ExchangeRelabel

/-!
# Independent Chart Index

The concrete relabeling that moves an arbitrary independent zero set to
the first block. The zero block follows from acyclicity and independence;
it is not an additional assumption about the selected chart.
-/
noncomputable section
namespace Verification.IndependentChartIndex
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (κ : Type) (n : ℕ) (I : Finset (Fin n))

abbrev Selected := {i : Fin n // i ∈ I}
abbrev Other := {i : Fin n // i ∉ I}

def split : Fin n ≃ Selected n I ⊕ Other n I := by
  classical
  exact (Equiv.sumCompl (I : Set (Fin n))).symm

def partners : (Fin n ⊕ Empty) ≃ Selected n I ⊕ Other n I :=
  (Equiv.sumEmpty (Fin n) Empty).trans (split n I)

def originals : (Fin n ⊕ κ) ≃ Selected n I ⊕ (Other n I ⊕ κ) :=
  (Equiv.sumCongr (split n I) (Equiv.refl κ)).trans
    (Equiv.sumAssoc (Selected n I) (Other n I) κ)

theorem partners_symm_left (i : Selected n I) : (partners n I).symm (Sum.inl i) = Sum.inl i.1 := rfl
theorem partners_symm_right (i : Other n I) : (partners n I).symm (Sum.inr i) = Sum.inl i.1 := rfl

theorem originals_symm_left (i : Selected n I) : (originals κ n I).symm (Sum.inl i) = Sum.inl i.1 := rfl
theorem originals_symm_middle (i : Other n I) : (originals κ n I).symm (Sum.inr (Sum.inl i)) = Sum.inl i.1 := rfl
theorem originals_symm_right (k : κ) : (originals κ n I).symm (Sum.inr (Sum.inr k)) = Sum.inr k := rfl

def matrix (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) :
    (Selected n I ⊕ (Other n I ⊕ κ)) → (Selected n I ⊕ Other n I) → ℤ :=
  fun a v => B ((originals κ n I).symm a) ((partners n I).symm v)

theorem matrix_left (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
    (a i : Selected n I) : matrix κ n I B (Sum.inl a) (Sum.inl i) = B (Sum.inl a.1) (Sum.inl i.1) := rfl

theorem independent_principal_zero (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hI : Independent (laterWeights κ n B) I)
    (a i : Fin n) (ha : a ∈ I) (hi : i ∈ I) : B (Sum.inl a) (Sum.inl i) = 0 := by
  have hu : (B (Sum.inl a) (Sum.inl i)).toNat = 0 := by
    by_cases hai : a < i
    · apply (hsupport a i).mpr
      by_contra hz
      exact hI a ha i hi (Or.inl ⟨hai, hz⟩)
    · exact hpos a i hai
  have hv : (-B (Sum.inl a) (Sum.inl i)).toNat = 0 := by
    by_cases hia : i < a
    · by_contra hz
      exact hI i hi a ha (Or.inl ⟨hia, hz⟩)
    · exact hneg a i hia
  exact le_antisymm (Int.toNat_eq_zero.mp hu) (neg_nonpos.mp (Int.toNat_eq_zero.mp hv))

theorem matrix_zero_block (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hI : Independent (laterWeights κ n B) I) :
    ∀ a i : Selected n I, matrix κ n I B (Sum.inl a) (Sum.inl i) = 0 := by
  intro a i
  exact independent_principal_zero κ n I B hpos hneg hsupport hI a.1 i.1 a.2 i.2

#print axioms Selected
#print axioms Other
#print axioms split
#print axioms partners
#print axioms originals
#print axioms partners_symm_left
#print axioms partners_symm_right
#print axioms originals_symm_left
#print axioms originals_symm_middle
#print axioms originals_symm_right
#print axioms matrix
#print axioms matrix_left
#print axioms independent_principal_zero
#print axioms matrix_zero_block
end Verification.IndependentChartIndex
