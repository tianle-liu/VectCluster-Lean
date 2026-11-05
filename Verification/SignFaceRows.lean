/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AnticliqueSubcolumns
import Mathlib.Algebra.BigOperators.Option
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic

/-!
# Sign Face Rows

The actual added sign coordinate on a codimension-one face: the
outside rows of I split as the new coordinate and the outside rows of I+j.
-/
noncomputable section
namespace Verification.SignFaceRows
open Verification.AnticliqueSubcolumns
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V]

def oldRow (I : Finset V) (j : V) (hj : j∉I) : Rows (C := C) I :=
  ⟨Sum.inl j,by intro v hv h; exact hj ((Sum.inl.inj h) ▸ hv)⟩

def retain (I : Finset V) (j : V) (a : Rows (C := C) (insert j I)) : Rows (C := C) I :=
  ⟨a.val,fun v hv => a.property v (Finset.mem_insert_of_mem hv)⟩

def addRow (I : Finset V) (j : V) (a : Rows (C := C) I)
    (ha : a.val≠Sum.inl j) : Rows (C := C) (insert j I) :=
  ⟨a.val,by intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv; exact ha; exact a.property v hv⟩

def rowEquiv (I : Finset V) (j : V) (hj : j∉I) :
    Option (Rows (C := C) (insert j I)) ≃ Rows (C := C) I := by
  classical
  exact {
    toFun a := match a with | none => oldRow I j hj | some a => retain I j a
    invFun a := if ha : a.val=Sum.inl j then none else some (addRow I j a ha)
    left_inv a := by
      cases a with
      | none => simp [oldRow]
      | some a => simp [retain,a.property j (Finset.mem_insert_self _ _),addRow]
    right_inv a := by
      by_cases ha : a.val=Sum.inl j
      · simp only [dif_pos ha]
        exact Subtype.ext ha.symm
      · simp only [dif_neg ha]
        rfl
  }

def extend (I : Finset V) (j : V) (hj : j∉I) :
    ((Rows (C := C) (insert j I) → ZMod 2) × ZMod 2) →ₗ[ZMod 2] (Rows (C := C) I → ZMod 2) where
  toFun x a := match (rowEquiv I j hj).symm a with | none => x.2 | some a => x.1 a
  map_add' x y := by funext a; simp only [Pi.add_apply]; cases (rowEquiv I j hj).symm a <;> rfl
  map_smul' r x := by funext a; simp only [Pi.smul_apply]; cases (rowEquiv I j hj).symm a <;> rfl

omit [Fintype V] [Fintype C] in
theorem extend_old (I : Finset V) (j : V) (hj : j∉I)
    (ε : Rows (C := C) (insert j I) → ZMod 2) (b : ZMod 2) :
    extend I j hj (ε,b) (oldRow I j hj)=b := by
  change (match (rowEquiv I j hj).symm (rowEquiv I j hj none) with | none => b | some a => ε a)=b
  rw [Equiv.symm_apply_apply]

omit [Fintype V] [Fintype C] in
theorem extend_retain (I : Finset V) (j : V) (hj : j∉I)
    (ε : Rows (C := C) (insert j I) → ZMod 2) (b : ZMod 2)
    (a : Rows (C := C) (insert j I)) : extend I j hj (ε,b) (retain I j a)=ε a := by
  change (match (rowEquiv I j hj).symm (rowEquiv I j hj (some a)) with | none => b | some a => ε a)=ε a
  rw [Equiv.symm_apply_apply]

theorem character_extension (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (ε : Rows (C := C) (insert j I) → ZMod 2) (b : ZMod 2) (i : V) :
    (∑ a : Rows (C := C) I, (B a.val i:ZMod 2)*extend I j hj (ε,b) a)=
      (B (Sum.inl j) i:ZMod 2)*b + ∑ a : Rows (C := C) (insert j I), (B a.val i:ZMod 2)*ε a := by
  rw [← (rowEquiv (C := C) I j hj).sum_comp (fun a => (B a.val i:ZMod 2)*extend I j hj (ε,b) a)]
  rw [Fintype.sum_option]
  simp only [rowEquiv,Equiv.coe_fn_mk]
  rw [extend_old]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [extend_retain]
  rfl

#print axioms oldRow
#print axioms retain
#print axioms addRow
#print axioms rowEquiv
#print axioms extend
#print axioms extend_old
#print axioms extend_retain
#print axioms character_extension
end Verification.SignFaceRows
