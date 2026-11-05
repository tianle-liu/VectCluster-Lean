/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RectangularMutationSplitting

/-!
# Rectangular Mutation Entries

The unimodular mutation factorization is the literal Fomin–Zelevinsky
rectangular matrix formula, not a freely chosen isomorphic matrix.
-/
noncomputable section
namespace Verification.RectangularMutationEntries
open Classical Verification.RectangularMutationSplitting
variable {V F : Type} [Fintype V] [DecidableEq V]
variable (B : Matrix (V⊕F) V ℤ) (k : V)

theorem column (i : V) : (fun a=>matrix B k a i)=map B k (Pi.single i 1) := by
  funext a
  rw [matrix,LinearMap.toMatrix'_apply]
  have he : (fun j : V=>if j=i then (1:ℤ) else 0)=Pi.single i 1 := by
    ext j
    simp [Pi.single_apply,eq_comm]
  exact congrArg (fun x=>map B k x a) he

theorem entry (hkk : B (Sum.inl k) k=0) (a : V⊕F) (i : V) :
    matrix B k a i=
      if a=Sum.inl k ∨ i=k then -B a i else
        B a i+max (B a k) 0*B (Sum.inl k) i+B a k*max (-B (Sum.inl k) i) 0 := by
  have hb (j : V) : B.mulVecLin (Pi.single j 1)=fun a=>B a j := by
    ext b
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [show matrix B k a i=map B k (Pi.single i 1) a from congrFun (column B k i) a]
  change rowEquiv B k (B.mulVecLin (columnEquiv B k (Pi.single i 1))) a=_
  rw [columnEquiv,Verification.IntegerShearReflection.column_single]
  by_cases hi : i=k
  · subst i
    simp only [ite_true,map_neg,hb]
    by_cases ha : a=Sum.inl k
    · subst a
      simp [rowEquiv,Verification.IntegerShearReflection.row,Verification.IntegerShearReflection.rowMap,hkk]
    · simp [rowEquiv,Verification.IntegerShearReflection.row,Verification.IntegerShearReflection.rowMap,ha,hkk]
  · simp only [if_neg hi,map_add,map_smul,hb]
    by_cases ha : a=Sum.inl k
    · subst a
      simp [rowEquiv,Verification.IntegerShearReflection.row,Verification.IntegerShearReflection.rowMap,hi,hkk]
    · simp [rowEquiv,Verification.IntegerShearReflection.row,Verification.IntegerShearReflection.rowMap,hi,ha,hkk]
      ring

theorem max_identity (a b : ℤ) :
    max a 0*b+a*max (-b) 0=max a 0*max b 0-max (-a) 0*max (-b) 0 := by
  by_cases ha : 0≤a <;> by_cases hb : 0≤b
  · rw [max_eq_left ha,max_eq_left hb,max_eq_right (by omega : -a≤0),max_eq_right (by omega : -b≤0)]
    ring
  · rw [max_eq_left ha,max_eq_right (by omega : b≤0),max_eq_right (by omega : -a≤0),max_eq_left (by omega : 0≤ -b)]
    ring
  · rw [max_eq_right (by omega : a≤0),max_eq_left hb,max_eq_left (by omega : 0≤ -a),max_eq_right (by omega : -b≤0)]
    ring
  · rw [max_eq_right (by omega : a≤0),max_eq_right (by omega : b≤0),max_eq_left (by omega : 0≤ -a),max_eq_left (by omega : 0≤ -b)]
    ring

theorem fz_entry (hkk : B (Sum.inl k) k=0) (a : V⊕F) (i : V) :
    matrix B k a i=
      if a=Sum.inl k ∨ i=k then -B a i else
        B a i+max (B a k) 0*max (B (Sum.inl k) i) 0-
          max (-B a k) 0*max (-B (Sum.inl k) i) 0 := by
  rw [entry B k hkk]
  split_ifs
  · rfl
  · rw [add_assoc,max_identity]
    ring

#print axioms column
#print axioms entry
#print axioms max_identity
#print axioms fz_entry
end Verification.RectangularMutationEntries
