/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RootedForestCertificate
import Verification.PathOrientationSigns

/-!
# Path Rooted Forest

Literal arbitrary-orientation path matrices have a rooted-forest
certificate, and their edge weights agree with the linear path matrix.
-/
noncomputable section
namespace Verification.PathRootedForest
open Verification.RootedForestCertificate

def path (n : ℕ) : Forest (Fin n) where
  parent i := if h : i.val=0 then none else some ⟨i.val-1,by omega⟩
  height i := i.val
  decrease i j h := by
    dsimp at h ⊢
    split at h
    · contradiction
    · rename_i hi
      have he := congrArg Fin.val (Option.some.inj h)
      change i.val-1=j.val at he
      omega

theorem parent (n : ℕ) (i j : Fin n) : (path n).parent i=some j ↔ i.val=j.val+1 := by
  dsimp [path]
  split
  · rename_i hi
    simp only [reduceCtorEq,false_iff]
    omega
  · rename_i hi
    simp only [Option.some.injEq,Fin.ext_iff]
    omega

theorem adjacent (n : ℕ) (i j : Fin n) :
    (path n).Adj i j ↔ j.val=i.val+1 ∨ i.val=j.val+1 := by
  simp only [Forest.Adj,parent]
  exact or_comm

theorem skew (a : ℕ→ℤˣ) (n : ℕ) (i j : Fin n) :
    PathOrientationSigns.matrix a n i j= -PathOrientationSigns.matrix a n j i := by
  simp only [PathOrientationSigns.matrix]
  ring

theorem support (a : ℕ→ℤˣ) (n : ℕ) (i j : Fin n) :
    PathOrientationSigns.matrix a n i j≠0 ↔ (path n).Adj i j := by
  rw [adjacent]
  by_cases h : j.val=i.val+1
  · have h' : i.val≠j.val+1 := by omega
    simp only [PathOrientationSigns.matrix,if_pos h,if_neg h',sub_zero]
    simp [h]
  · by_cases h' : i.val=j.val+1
    · simp only [PathOrientationSigns.matrix,if_neg h,if_pos h',zero_sub]
      simp [h']
    · simp only [PathOrientationSigns.matrix,if_neg h,if_neg h',sub_self]
      simp [h,h']

theorem absolute (a : ℕ→ℤˣ) (n : ℕ) (i j : Fin n) :
    |PathOrientationSigns.matrix a n i j|=|PathLattice.pathMatrix n i j| := by
  have hu (u : ℤˣ) : |(u:ℤ)|=1 := by
    rcases Int.isUnit_iff.mp u.isUnit with h|h <;> simp [h]
  by_cases h : j.val=i.val+1
  · have h' : i.val≠j.val+1 := by omega
    simp only [PathOrientationSigns.matrix,PathLattice.pathMatrix,if_pos h,if_neg h',sub_zero]
    exact hu _
  · by_cases h' : i.val=j.val+1
    · simp only [PathOrientationSigns.matrix,PathLattice.pathMatrix,if_neg h,if_pos h',zero_sub,abs_neg]
      exact hu _
    · simp only [PathOrientationSigns.matrix,PathLattice.pathMatrix,if_neg h,if_neg h']

#print axioms path
#print axioms parent
#print axioms adjacent
#print axioms skew
#print axioms support
#print axioms absolute
end Verification.PathRootedForest
