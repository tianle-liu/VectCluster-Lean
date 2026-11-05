/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRightEndpoint

/-!
# Path Endpoint Words

Literal normalized words for the constant-endpoint quotient bases.
-/

namespace Verification.PathEndpointWords

open Classical Verification.PathRhoWords Verification.PathRhoEndpoint

variable {R : Type*} [CommRing R]

def normalizeLeft : List Bool → List Bool
  | [] => []
  | _::tail => false::tail

def normalizeRight : List Bool → List Bool
  | [] => []
  | [_] => [false]
  | a::b::tail => a::normalizeRight (b::tail)

def leftScalar (k : R) : List Bool → R
  | [] => 1
  | a::_ => evaluation k a

def rightScalar (k : R) : List Bool → R
  | [] => 1
  | [a] => evaluation k a
  | _::b::tail => rightScalar k (b::tail)

def LeftNormal (w : List Bool) : Prop := normalizeLeft w=w
def RightNormal (w : List Bool) : Prop := normalizeRight w=w
def BothNormal (w : List Bool) : Prop := LeftNormal w ∧ RightNormal w

theorem normalizeLeft_length (w : List Bool) : (normalizeLeft w).length=w.length := by
  cases w <;> rfl

theorem normalizeRight_length (w : List Bool) : (normalizeRight w).length=w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases w with
    | nil => rfl
    | cons b tail => simpa only [normalizeRight,List.length_cons] using congrArg Nat.succ ih

theorem normalizeLeft_idempotent (w : List Bool) : LeftNormal (normalizeLeft w) := by
  cases w <;> rfl

theorem normalizeRight_idempotent (w : List Bool) : RightNormal (normalizeRight w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases w with
    | nil => rfl
    | cons b tail =>
      have hlen := normalizeRight_length (b::tail)
      cases he : normalizeRight (b::tail) with
      | nil => rw [he] at hlen; simp only [List.length_nil,List.length_cons] at hlen; omega
      | cons c rest =>
        change normalizeRight (a::normalizeRight (b::tail))=a::normalizeRight (b::tail)
        rw [he,normalizeRight]
        change normalizeRight (normalizeRight (b::tail))=normalizeRight (b::tail) at ih
        rw [he] at ih
        rw [ih]

theorem normalizations_commute (w : List Bool) :
    normalizeLeft (normalizeRight w)=normalizeRight (normalizeLeft w) := by
  cases w with
  | nil => rfl
  | cons a w =>
    cases w with
    | nil => rfl
    | cons b tail => rfl

theorem both_normalized (w : List Bool) : BothNormal (normalizeLeft (normalizeRight w)) := by
  constructor
  · exact normalizeLeft_idempotent _
  · change normalizeRight (normalizeLeft (normalizeRight w))=normalizeLeft (normalizeRight w)
    rw [← normalizations_commute,normalizeRight_idempotent]

theorem left_scalar_normal (k : R) (w : List Bool) (hw : LeftNormal w) : leftScalar k w=1 := by
  cases w with
  | nil => rfl
  | cons a tail =>
    have ha : false=a := (List.cons.inj hw).1
    rw [← ha]
    rfl

theorem right_scalar_normal (k : R) (w : List Bool) (hw : RightNormal w) : rightScalar k w=1 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases w with
    | nil =>
      have ha : false=a := (List.cons.inj hw).1
      rw [← ha]
      rfl
    | cons b tail =>
      exact ih (List.cons.inj hw).2

theorem left_projection_column (k : R) (w : List Bool) :
    Verification.PathLeftEndpoint.projection k (Finsupp.single w 1)=
      leftScalar k w • Finsupp.single (normalizeLeft w) 1 := by
  rw [Verification.PathLeftEndpoint.projection_single]
  cases w with
  | nil => exact (one_smul _ _).symm
  | cons a tail => rfl

theorem right_projection_column (k : R) (w : List Bool) :
    Verification.PathRightEndpoint.projection k (Finsupp.single w 1)=
      rightScalar k w • Finsupp.single (normalizeRight w) 1 := by
  rw [Verification.PathRightEndpoint.projection_single]
  induction w with
  | nil => exact (one_smul _ _).symm
  | cons a w ih =>
    cases w with
    | nil => rfl
    | cons b tail =>
      rw [Verification.PathRightEndpoint.projectionColumn,ih,map_smul,prepend_single]
      rfl

theorem left_projection_fixed (k : R) (w : List Bool) (hw : LeftNormal w) :
    Verification.PathLeftEndpoint.projection k (Finsupp.single w 1)=Finsupp.single w 1 := by
  rw [left_projection_column,left_scalar_normal k w hw,hw,one_smul]

theorem right_projection_fixed (k : R) (w : List Bool) (hw : RightNormal w) :
    Verification.PathRightEndpoint.projection k (Finsupp.single w 1)=Finsupp.single w 1 := by
  rw [right_projection_column,right_scalar_normal k w hw,hw,one_smul]

#print axioms normalizeLeft
#print axioms normalizeRight
#print axioms leftScalar
#print axioms rightScalar
#print axioms LeftNormal
#print axioms RightNormal
#print axioms BothNormal
#print axioms normalizeLeft_length
#print axioms normalizeRight_length
#print axioms normalizeLeft_idempotent
#print axioms normalizeRight_idempotent
#print axioms normalizations_commute
#print axioms both_normalized
#print axioms left_scalar_normal
#print axioms right_scalar_normal
#print axioms left_projection_column
#print axioms right_projection_column
#print axioms left_projection_fixed
#print axioms right_projection_fixed

end Verification.PathEndpointWords
