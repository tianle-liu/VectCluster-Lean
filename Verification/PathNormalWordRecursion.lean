/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathNormalizedBasis

/-!
# Path Normal Word Recursion

Exact removal of the extra initial coordinate in the open path pieces.
-/

namespace Verification.PathNormalWordRecursion

open Classical Verification.PathEndpointWords Verification.PathNormalizedBasis

theorem rightNormal_cons (a : Bool) (w : List Bool) (hw : w ≠ []) :
    RightNormal (a::w) ↔ RightNormal w := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons b tail => simp only [RightNormal,normalizeRight,List.cons.injEq,true_and]

theorem leftNormal_cons (a : Bool) (w : List Bool) : LeftNormal (a::w) ↔ a=false := by
  simp only [LeftNormal,normalizeLeft,List.cons.injEq,and_true,eq_comm]

theorem tail_length (n : ℕ) (B : List Bool → Prop) (x : NormalWord B (n+1)) : x.val.tail.length=n := by
  rw [List.length_tail,x.property.1,Nat.add_sub_cancel]

theorem tail_rightNormal (n : ℕ) (hn : 0 < n) (w : List Bool) (hl : w.length=n+1)
    (hw : RightNormal w) : RightNormal w.tail := by
  cases w with
  | nil => simp only [List.length_nil] at hl; omega
  | cons a tail =>
    have ht : tail ≠ [] := by intro he; rw [he] at hl; simp only [List.length_cons,List.length_nil] at hl; omega
    exact (rightNormal_cons a tail ht).mp hw

/-- The free old endpoint is a genuine two-element torus basis factor. -/
noncomputable def rightEquiv (n : ℕ) (hn : 0 < n) :
    NormalWord RightNormal (n+1) ≃ Bool × NormalWord RightNormal n where
  toFun x := (x.val.headD false,⟨x.val.tail,tail_length n RightNormal x,
    tail_rightNormal n hn x.val x.property.1 x.property.2⟩)
  invFun x := ⟨x.1::x.2.val,by
    constructor
    · simp only [List.length_cons,x.2.property.1]
    · apply (rightNormal_cons x.1 x.2.val _).mpr x.2.property.2
      intro h
      have hh := x.2.property.1
      rw [h] at hh
      simp only [List.length_nil] at hh
      omega⟩
  left_inv x := by
    apply Subtype.ext
    have hl := x.property.1
    cases he : x.val with
    | nil => rw [he] at hl; simp only [List.length_nil] at hl; omega
    | cons a tail =>
      change x.val.headD false::x.val.tail=a::tail
      rw [he]
      rfl
  right_inv _ := rfl

/-- A fixed initial endpoint contributes no torus basis factor. -/
noncomputable def bothEquiv (n : ℕ) (hn : 0 < n) :
    NormalWord BothNormal (n+1) ≃ NormalWord RightNormal n where
  toFun x := ⟨x.val.tail,tail_length n BothNormal x,
    tail_rightNormal n hn x.val x.property.1 x.property.2.2⟩
  invFun x := ⟨false::x.val,by
    constructor
    · simp only [List.length_cons,x.property.1]
    · constructor
      · rfl
      · apply (rightNormal_cons false x.val _).mpr x.property.2
        intro h
        have hh := x.property.1
        rw [h] at hh
        simp only [List.length_nil] at hh
        omega⟩
  left_inv x := by
    apply Subtype.ext
    have hl := x.property.1
    have hw := x.property.2.1
    cases he : x.val with
    | nil => rw [he] at hl; simp only [List.length_nil] at hl; omega
    | cons a tail =>
      rw [he] at hw
      have ha := (leftNormal_cons a tail).mp hw
      change false::x.val.tail=a::tail
      rw [he,ha]
      rfl
  right_inv _ := rfl

#print axioms rightNormal_cons
#print axioms leftNormal_cons
#print axioms tail_length
#print axioms tail_rightNormal
#print axioms rightEquiv
#print axioms bothEquiv

end Verification.PathNormalWordRecursion
