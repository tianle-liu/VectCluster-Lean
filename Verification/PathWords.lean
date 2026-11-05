/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.Path
import Mathlib.Data.List.Count

/-!
# Path Words

Actual binary words underlying the path's square-free monomial generators.
Run decomposition is proved to be a bijection, including the empty word and
both boundary runs. Thus the existing run-transfer theorem can be applied to
original word generators rather than assumed to describe them.
-/

namespace Verification.PathWords

/-- Add selected positions at the start of the first run. -/
def addHead (k : ℕ) : List ℕ → List ℕ
  | [] => [k]
  | a :: tail => (a+k) :: tail

/-- The unique run vector, including zero-length runs between consecutive vacancies. -/
def runs : List Bool → List ℕ
  | [] => [0]
  | false :: w => 0 :: runs w
  | true :: w => addHead 1 (runs w)

/-- Reassemble a binary word from a nonempty run vector. -/
def encode : List ℕ → List Bool
  | [] => []
  | a :: tail => List.replicate a true ++
      match tail with
      | [] => []
      | _ :: _ => false :: encode tail

theorem runs_ne_nil (w : List Bool) : runs w ≠ [] := by
  induction w with
  | nil => simp [runs]
  | cons b w ih =>
    cases b
    · simp [runs]
    · simp only [runs]
      cases h : runs w <;> simp [addHead]

theorem encode_addHead (a : ℕ) (r : List ℕ) (hr : r ≠ []) :
    encode (addHead a r)=List.replicate a true ++ encode r := by
  cases r with
  | nil => exact (hr rfl).elim
  | cons b tail =>
    simp only [addHead,encode]
    rw [Nat.add_comm b a,List.replicate_add,List.append_assoc]

theorem encode_runs (w : List Bool) : encode (runs w)=w := by
  induction w with
  | nil => simp [runs,encode]
  | cons b w ih =>
    cases b
    · have hn := runs_ne_nil w
      cases h : runs w with
      | nil => exact (hn h).elim
      | cons a tail => simpa only [runs,h,encode,List.replicate_zero,List.nil_append] using congrArg (List.cons false) ih
    · rw [runs,encode_addHead 1 (runs w) (runs_ne_nil w),ih]
      simp

theorem runs_replicate_append (a b : ℕ) (tail : List ℕ) (w : List Bool)
    (hw : runs w=b :: tail) :
    runs (List.replicate a true ++ w)=(b+a) :: tail := by
  induction a with
  | zero => simpa using hw
  | succ a ih =>
    simp only [List.replicate_succ,List.cons_append,runs,ih,addHead]
    congr 1

theorem runs_encode (r : List ℕ) (hr : r ≠ []) : runs (encode r)=r := by
  induction r with
  | nil => exact (hr rfl).elim
  | cons a tail ih =>
    cases tail with
    | nil =>
      simpa only [encode,List.append_nil,Nat.zero_add] using
        runs_replicate_append a 0 [] [] rfl
    | cons b tail =>
      have ht := ih (by simp)
      simpa only [encode,Nat.zero_add] using
        runs_replicate_append a 0 (b :: tail) (false :: encode (b :: tail))
          (by simp only [runs,ht])

theorem encode_length (r : List ℕ) (hr : r ≠ []) :
    (encode r).length+1=r.sum+r.length := by
  induction r with
  | nil => exact (hr rfl).elim
  | cons a tail ih =>
    cases tail with
    | nil => simp [encode]
    | cons b tail =>
      have ht := ih (by simp)
      simp only [encode,List.length_append,List.length_replicate,List.length_cons,
        List.sum_cons] at *
      omega

theorem runs_length_weight (w : List Bool) : (runs w).sum+(runs w).length=w.length+1 := by
  have h := encode_length (runs w) (runs_ne_nil w)
  rw [encode_runs] at h
  exact h.symm

/-- The total run length is the literal number of selected monomial positions. -/
theorem runs_sum (w : List Bool) : (runs w).sum=w.count true := by
  induction w with
  | nil => simp [runs]
  | cons b w ih =>
    cases b
    · simpa [runs] using ih
    · cases h : runs w with
      | nil => exact (runs_ne_nil w h).elim
      | cons a tail =>
        simp only [runs,h,addHead,List.sum_cons] at *
        simp only [List.count_cons_self]
        omega

/-- Actual binary words of the given length. -/
abbrev Word (n : ℕ) := {w : List Bool // w.length=n}

/-- Their actual run vectors; the equation records selected positions plus vacancies. -/
abbrev RunVector (n : ℕ) := {r : List ℕ // r ≠ [] ∧ r.sum+r.length=n+1}

/-- The precise word/run bijection used for the path-cokernel computation. -/
def wordRunEquiv (n : ℕ) : Word n ≃ RunVector n where
  toFun w := ⟨runs w.val,runs_ne_nil _,by rw [runs_length_weight,w.property]⟩
  invFun r := ⟨encode r.val,by
    have h := encode_length r.val r.property.1
    have hr := r.property.2
    omega⟩
  left_inv w := Subtype.ext (encode_runs w.val)
  right_inv r := Subtype.ext (runs_encode r.val r.property.1)

#print axioms runs_sum
#print axioms addHead
#print axioms runs
#print axioms encode
#print axioms runs_ne_nil
#print axioms encode_addHead
#print axioms encode_runs
#print axioms runs_replicate_append
#print axioms runs_encode
#print axioms encode_length
#print axioms runs_length_weight
#print axioms Word
#print axioms RunVector
#print axioms wordRunEquiv

end Verification.PathWords
