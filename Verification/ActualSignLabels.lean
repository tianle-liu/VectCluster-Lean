/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MatrixSignLabels
import Verification.AnticliqueSubcolumns

/-!
# Actual Sign Labels

The manuscript's literal affine F₂ sign equations on coordinates
outside an independent zero set. AS gives coordinates, nonemptiness,
the precise cardinality, and the half-dimension bound.
-/
noncomputable section
namespace Verification.ActualSignLabels
open Verification.PrimitiveSignFiber Verification.AnticliqueSubcolumns
variable {V C : Type*} [Fintype V] [Fintype C]

def remainingEquiv (I : Finset V) : Rows (C := C) I ≃ ({v : V // v ∉ I} ⊕ C) where
  toFun a := by
    rcases a with ⟨a,h⟩
    cases a with
    | inl v => exact Sum.inl ⟨v,fun hv => h v hv rfl⟩
    | inr c => exact Sum.inr c
  invFun a := match a with
    | Sum.inl v => ⟨Sum.inl v.val,by
        intro w hw h
        have := Sum.inl.inj h
        exact v.property (this ▸ hw)⟩
    | Sum.inr c => ⟨Sum.inr c,by simp⟩
  left_inv a := by rcases a with ⟨a,h⟩; cases a <;> rfl
  right_inv a := by cases a <;> rfl

theorem card_remaining (I : Finset V) :
    Fintype.card (Rows (C := C) I)=Fintype.card V-I.card+Fintype.card C := by
  classical
  rw [Fintype.card_congr (remainingEquiv (C := C) I),Fintype.card_sum,
    Fintype.card_subtype_compl]
  simp

theorem residual_dimension (I : Finset V) :
    Fintype.card (Rows (C := C) I)-Fintype.card I=
      Fintype.card V+Fintype.card C-2*I.card := by
  rw [card_remaining,Fintype.card_coe]
  have := Finset.card_le_univ I
  omega

def labels (B : (V ⊕ C) → V → ℤ) (I : Finset V) :=
  {x : Rows (C := C) I → Bit // ∀ i : I, ∑ a, (B a.val i.val : Bit)*x a=1}

theorem selected_single (B : (V ⊕ C) → V → ℤ) (I : Finset V) (i : I)
    (a : Rows (C := C) I) : selectedMap B I (Finsupp.single i 1) a=B a.val i.val := by
  simp [selectedMap,column]

def matrixEquiv (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    labels B I ≃ Verification.MatrixSignLabels.labels (selectedMap B I) (fun _ => 1) :=
  Equiv.subtypeEquivRight (fun _ => by simp only [selected_single])

def coordinates (B : (V ⊕ C) → V → ℤ) (I : Finset V) (h : AS B I) :
    labels B I ≃ (Fin (Fintype.card V+Fintype.card C-2*I.card) → Bit) :=
  ((matrixEquiv B I).trans
    (Verification.MatrixSignLabels.coordinates (selectedMap B I) (fun _ => 1) h.1 h.2)).trans
      (Equiv.piCongrLeft' (fun _ => Bit) (finCongr (residual_dimension I)))

theorem card_labels (B : (V ⊕ C) → V → ℤ) (I : Finset V) (h : AS B I) :
    Nat.card (labels B I)=2^(Fintype.card V+Fintype.card C-2*I.card) := by
  rw [Nat.card_congr (coordinates B I h)]
  simp [Nat.card_eq_fintype_card,Bit]

theorem nonempty_labels (B : (V ⊕ C) → V → ℤ) (I : Finset V) (h : AS B I) :
    Nonempty (labels B I) := ⟨(coordinates B I h).symm 0⟩

theorem twice_card_le_dimension (B : (V ⊕ C) → V → ℤ) (I : Finset V) (h : AS B I) :
    2*I.card ≤ Fintype.card V+Fintype.card C := by
  have hr := Verification.PrimitiveTorusRank.quotient_rank (selectedMap B I)
    (Finsupp.basisSingleOne : Basis I ℤ (I →₀ ℤ)) h.1 h.2
  rw [card_remaining,Fintype.card_coe] at hr
  have := Finset.card_le_univ I
  omega

#print axioms remainingEquiv
#print axioms card_remaining
#print axioms residual_dimension
#print axioms labels
#print axioms selected_single
#print axioms matrixEquiv
#print axioms coordinates
#print axioms card_labels
#print axioms nonempty_labels
#print axioms twice_card_le_dimension
end Verification.ActualSignLabels
