/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualSignLabels

/-!
# Real Stratum Indices

Exact reindexing of original mutable and frozen coordinates for a zero set.
-/
noncomputable section
namespace Verification.RealStratumIndices
open Verification.AnticliqueSubcolumns
variable {V C : Type*}

def Outside (I : Finset V) := {v : V // v∉I}

def mutableEquiv (I : Finset V) : (I ⊕ Outside I) ≃ V := by
  classical
  exact Equiv.sumCompl (fun v => v∈I)

def rowEquiv (I : Finset V) : (I ⊕ Rows (C := C) I) ≃ (V ⊕ C) :=
  ((Equiv.sumCongr (Equiv.refl I) (ActualSignLabels.remainingEquiv I)).trans
    (Equiv.sumAssoc I (Outside I) C).symm).trans
      (Equiv.sumCongr (mutableEquiv I) (Equiv.refl C))

def remainingMutable (I : Finset V) (v : Outside I) : Rows (C := C) I :=
  (ActualSignLabels.remainingEquiv I).symm (Sum.inl v)

theorem mutable_inl (I : Finset V) (i : I) : mutableEquiv I (Sum.inl i)=i.val := rfl

theorem mutable_inr (I : Finset V) (v : Outside I) : mutableEquiv I (Sum.inr v)=v.val := rfl

theorem row_inl (I : Finset V) (i : I) : rowEquiv (C := C) I (Sum.inl i)=Sum.inl i.val := rfl

theorem row_inr (I : Finset V) (a : Rows (C := C) I) : rowEquiv I (Sum.inr a)=a.val := by
  rcases a with ⟨a,h⟩
  cases a <;> rfl

theorem remainingMutable_val (I : Finset V) (v : Outside I) :
    (remainingMutable (C := C) I v).val=Sum.inl v.val := rfl

def matrix (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    (I ⊕ Rows (C := C) I) → (I ⊕ Outside I) → ℤ :=
  fun a v => B (rowEquiv I a) (mutableEquiv I v)

theorem matrix_zero_block (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hB : ∀ a i : I, B (Sum.inl a.val) i.val=0) :
    ∀ a i : I, matrix B I (Sum.inl a) (Sum.inl i)=0 := hB

theorem matrix_reduced (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (a : Rows (C := C) I) (i : I) : matrix B I (Sum.inr a) (Sum.inl i)=B a.val i.val := by
  simp only [matrix,row_inr,mutable_inl]

#print axioms Outside
#print axioms mutableEquiv
#print axioms rowEquiv
#print axioms remainingMutable
#print axioms mutable_inl
#print axioms mutable_inr
#print axioms row_inl
#print axioms row_inr
#print axioms remainingMutable_val
#print axioms matrix
#print axioms matrix_zero_block
#print axioms matrix_reduced
end Verification.RealStratumIndices
