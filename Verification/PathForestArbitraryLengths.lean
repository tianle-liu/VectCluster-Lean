/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestMatrixPredicate

/-!
# Path Forest Arbitrary Lengths

Arbitrary path lengths, including zero, are converted to the even/odd
component convention of the manuscript's path-forest predicate.
-/
noncomputable section
namespace Verification.PathForestArbitraryLengths
open Classical Verification.PathForestMatrixPredicate Verification.PathForestOrientation

theorem parity (n : ℕ) : PathOrientationBlocks.length (n/2) (decide (n%2=1))=n := by
  by_cases h : n%2=1
  · simp only [h,decide_true,PathOrientationBlocks.length]
    omega
  · simp only [h,decide_false,PathOrientationBlocks.length]
    omega

variable {S : Type} [Fintype S] (l : S→ℕ) (a : S→ℕ→ℤˣ)
def coordinates : Vertex (fun s=>l s/2) (fun s=>decide (l s%2=1))≃(Σs,Fin (l s)) :=
  Equiv.sigmaCongrRight (fun s=>finCongr (parity (l s)))

omit [Fintype S] in
theorem entry (i j : Vertex (fun s=>l s/2) (fun s=>decide (l s%2=1))) :
    Matrix.blockDiagonal' (fun s=>PathOrientationSigns.matrix (a s) (l s))
      (coordinates l i) (coordinates l j)=matrix (fun s=>l s/2) (fun s=>decide (l s%2=1)) a i j := by
  rcases i with ⟨s,i⟩
  rcases j with ⟨t,j⟩
  change Matrix.blockDiagonal' (fun s=>PathOrientationSigns.matrix (a s) (l s))
    ⟨s,finCongr (parity (l s)) i⟩ ⟨t,finCongr (parity (l t)) j⟩=_
  unfold matrix
  by_cases h : s=t
  · subst t
    rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    rfl
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h]

theorem block (n : ℕ) (e : (Σs,Fin (l s))≃Fin n) (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀i j,A (e i) (e j)=Matrix.blockDiagonal' (fun s=>PathOrientationSigns.matrix (a s) (l s)) i j) :
    IsPathForest n A := by
  refine ⟨S,inferInstance,fun s=>l s/2,fun s=>decide (l s%2=1),a,(coordinates l).trans e,?_⟩
  intro i j
  exact (h (coordinates l i) (coordinates l j)).trans (entry l a i j)

def singleCoordinates (n : ℕ) : (Σ_ : PUnit,Fin n)≃Fin n where
  toFun x:=x.2
  invFun i:=⟨PUnit.unit,i⟩
  left_inv x:=by rcases x with ⟨⟨⟩,i⟩;rfl
  right_inv _:=rfl

theorem single (n : ℕ) (a : ℕ→ℤˣ) : IsPathForest n (PathOrientationSigns.matrix a n) := by
  letI : DecidableEq PUnit := Classical.decEq _
  apply block (fun _ : PUnit=>n) (fun _=>a) n (singleCoordinates n)
  rintro ⟨⟨⟩,i⟩ ⟨⟨⟩,j⟩
  rw [Matrix.blockDiagonal'_apply_eq]
  rfl

#print axioms parity
#print axioms coordinates
#print axioms entry
#print axioms block
#print axioms singleCoordinates
#print axioms single
end Verification.PathForestArbitraryLengths
