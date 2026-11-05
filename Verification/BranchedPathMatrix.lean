/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOrientationSigns
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option

/-!
# Branched Path Matrix

The standard branching-vertex presentation of types D and E.
The two central edge entries may be arbitrary here: after deleting the
central vertex the actual remaining matrix is the stated path forest.
-/
noncomputable section
namespace Verification.BranchedPathMatrix
open Classical
variable {S : Type} [Fintype S] (length : S → ℕ) (a : S → ℕ → ℤˣ)
abbrev Branches := Σ s,Fin (length s)
abbrev Vertices := Option (Branches length)

def matrix (up down : S → ℤ) : Matrix (Vertices length) (Vertices length) ℤ
  | none,none => 0
  | none,some ⟨s,i⟩ => if i.val=0 then up s else 0
  | some ⟨s,i⟩,none => if i.val=0 then down s else 0
  | some i,some j => Matrix.blockDiagonal' (fun s => PathOrientationSigns.matrix (a s) (length s)) i j

def deletion : Branches length ↪ Vertices length := ⟨some,Option.some_injective _⟩

omit [Fintype S] in
theorem deletion_range (w : Vertices length) : w∈Set.range (deletion length) ↔ w≠none := by
  cases w <;> simp [deletion]

omit [Fintype S] in
theorem deletion_matrix (up down : S → ℤ) (i j : Branches length) :
    matrix length a up down (deletion length i) (deletion length j)=
      Matrix.blockDiagonal' (fun s => PathOrientationSigns.matrix (a s) (length s)) i j := rfl

#print axioms Branches
#print axioms Vertices
#print axioms matrix
#print axioms deletion
#print axioms deletion_range
#print axioms deletion_matrix
end Verification.BranchedPathMatrix
