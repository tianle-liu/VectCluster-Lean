/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathNormalWordRecursion
import Verification.PathWords

/-!
# Path Endpoint Word Removal

Exact finite basis bijections deleting the constant endpoint slots.
Their codomains are the binary words used in the proved kill/slide cokernel.
-/

namespace Verification.PathEndpointWordRemoval

open Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathNormalWordRecursion

theorem rightNormal_append_false (w : List Bool) : RightNormal (w++[false]) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    exact (rightNormal_cons a (w++[false]) (by simp)).mpr ih

theorem normalizeRight_dropLast (w : List Bool) (hw : w ≠ []) :
    normalizeRight w=w.dropLast++[false] := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons a w ih =>
    cases w with
    | nil => rfl
    | cons b tail =>
      rw [normalizeRight,List.dropLast_cons₂,List.cons_append]
      exact congrArg (List.cons a) (ih (List.cons_ne_nil _ _))

/-- A fixed right coordinate contributes exactly one forced false slot. -/
noncomputable def rightWordEquiv (n : ℕ) :
    NormalWord RightNormal (n+1) ≃ Verification.PathWords.Word n where
  toFun w := ⟨w.val.dropLast,by rw [List.length_dropLast,w.property.1]; omega⟩
  invFun w := ⟨w.val++[false],by simp only [List.length_append,w.property,List.length_singleton],
    rightNormal_append_false w.val⟩
  left_inv w := by
    apply Subtype.ext
    have hn : w.val ≠ [] := by
      intro he
      have hh := w.property.1
      rw [he] at hh
      simp only [List.length_nil] at hh
      omega
    change w.val.dropLast++[false]=w.val
    rw [← normalizeRight_dropLast w.val hn]
    exact w.property.2
  right_inv w := by
    apply Subtype.ext
    exact List.dropLast_concat

noncomputable def bothWordEquiv (n : ℕ) :
    NormalWord BothNormal (n+2) ≃ Verification.PathWords.Word n :=
  (Verification.PathNormalWordRecursion.bothEquiv (n+1) (by omega)).trans (rightWordEquiv n)

theorem rightWordEquiv_word (n : ℕ) (w : NormalWord RightNormal (n+1)) :
    (rightWordEquiv n w).val=w.val.dropLast := rfl

theorem rightWordEquiv_inverse (n : ℕ) (w : Verification.PathWords.Word n) :
    ((rightWordEquiv n).symm w).val=w.val++[false] := rfl

theorem bothWordEquiv_word (n : ℕ) (w : NormalWord BothNormal (n+2)) :
    (bothWordEquiv n w).val=w.val.tail.dropLast := rfl

theorem bothWordEquiv_inverse (n : ℕ) (w : Verification.PathWords.Word n) :
    ((bothWordEquiv n).symm w).val=false::(w.val++[false]) := rfl

#print axioms rightNormal_append_false
#print axioms normalizeRight_dropLast
#print axioms rightWordEquiv
#print axioms bothWordEquiv
#print axioms rightWordEquiv_word
#print axioms rightWordEquiv_inverse
#print axioms bothWordEquiv_word
#print axioms bothWordEquiv_inverse

end Verification.PathEndpointWordRemoval
