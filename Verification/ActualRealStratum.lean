/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealExchangeStratum
import Verification.RealStratumIndices
import Verification.RealAffineComponents

/-!
# Actual Real Stratum

Real zero strata with the manuscript's literal mutable/frozen indices.
The exchange equations and Euclidean subspace topology are retained.
-/
noncomputable section
namespace Verification.ActualRealStratum
open Verification.RealStratumIndices Verification.AnticliqueSubcolumns
open Verification.RealExchangeCharacters
variable {V C : Type*} [Fintype V] [Fintype C]

def Point (B : (V ⊕ C) → V → ℤ) (I : Finset V) :=
  {p : ((V ⊕ C) → ℝ) × (V → ℝ) //
    (∀ i : I, p.1 (Sum.inl i.val)=0) ∧ (∀ a : Rows (C := C) I, p.1 a.val≠0) ∧
      ∀ v, p.1 (Sum.inl v)*p.2 v=exchange p.1 (fun a => B a v)}

instance pointTopology (B : (V ⊕ C) → V → ℤ) (I : Finset V) : TopologicalSpace (Point B I) :=
  inferInstanceAs (TopologicalSpace {p : ((V ⊕ C) → ℝ) × (V → ℝ) //
    (∀ i : I, p.1 (Sum.inl i.val)=0) ∧ (∀ a : Rows (C := C) I, p.1 a.val≠0) ∧
      ∀ v, p.1 (Sum.inl v)*p.2 v=exchange p.1 (fun a => B a v)})

def ambientCoordinates (I : Finset V) : (((V ⊕ C) → ℝ) × (V → ℝ)) ≃ₜ
    (((I ⊕ Rows (C := C) I) → ℝ) × ((I ⊕ Outside I) → ℝ)) :=
  (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (rowEquiv I)).symm.prodCongr
    (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (mutableEquiv I)).symm

theorem exchange_reindex (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (x : (V ⊕ C) → ℝ) (v : I ⊕ Outside I) :
    exchange (fun a => x (rowEquiv I a)) (fun a => matrix B I a v)=
      exchange x (fun a => B a (mutableEquiv I v)) := by
  unfold exchange matrix
  rw [(rowEquiv I).prod_comp (fun a => x a^(B a (mutableEquiv I v)).toNat),
    (rowEquiv I).prod_comp (fun a => x a^(-B a (mutableEquiv I v)).toNat)]

omit [Fintype V] [Fintype C] in
theorem initial_reindex (I : Finset V) (x : (V ⊕ C) → ℝ) (v : I ⊕ Outside I) :
    RealExchangeStratum.initial (remainingMutable (C := C) I) (fun a => x (rowEquiv I a)) v=
      x (Sum.inl (mutableEquiv I v)) := by
  cases v with
  | inl i => rfl
  | inr v => rw [RealExchangeStratum.initial,Sum.elim_inr,row_inr,remainingMutable_val,mutable_inr]

def splitCoordinates (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    Point B I ≃ₜ RealExchangeStratum.Point (remainingMutable (C := C) I) (matrix B I) := by
  apply (ambientCoordinates (C := C) I).subtype
  intro p
  change ((∀ i : I, p.1 (Sum.inl i.val)=0) ∧ (∀ a : Rows (C := C) I, p.1 a.val≠0) ∧
      ∀ v, p.1 (Sum.inl v)*p.2 v=exchange p.1 (fun a => B a v)) ↔
    ((∀ i : I, p.1 (rowEquiv I (Sum.inl i))=0) ∧
      (∀ a : Rows (C := C) I, p.1 (rowEquiv I (Sum.inr a))≠0) ∧
      ∀ v, RealExchangeStratum.initial (remainingMutable (C := C) I)
          (fun a => p.1 (rowEquiv I a)) v * p.2 (mutableEquiv I v)=
        exchange (fun a => p.1 (rowEquiv I a)) (fun a => matrix B I a v))
  simp only [row_inl,row_inr,initial_reindex,exchange_reindex]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact (mutableEquiv I).surjective.forall

def coordinates (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hB : ∀ a i : I, B (Sum.inl a.val) i.val=0) : Point B I ≃ₜ RealAffineComponents.stratum B I := by
  have hmat : RealExchangeStratum.reduced (matrix B I)=
      fun (a : Rows (C := C) I) (i : I) => B a.val i.val := by
    funext a i
    exact matrix_reduced B I a i
  have e := (splitCoordinates B I).trans
    (RealExchangeStratum.coordinates (remainingMutable (C := C) I) (matrix B I)
      (matrix_zero_block B I hB))
  rw [hmat] at e
  exact e

#print axioms Point
#print axioms pointTopology
#print axioms ambientCoordinates
#print axioms exchange_reindex
#print axioms initial_reindex
#print axioms splitCoordinates
#print axioms coordinates
end Verification.ActualRealStratum
