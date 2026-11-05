/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RectangularMutationEntries

/-!
# Rectangular Source Sink Mutation

At a source or sink the literal rectangular mutation only reverses
incident principal arrows. Skew symmetry and principal zero entries persist.
-/
noncomputable section
namespace Verification.RectangularSourceSinkMutation
open Classical Verification.RectangularMutationSplitting Verification.RectangularMutationEntries
variable {V F : Type} [Fintype V] [DecidableEq V]
variable (B : Matrix (V⊕F) V ℤ)
def Skew : Prop := ∀i j,B (Sum.inl i) j= -B (Sum.inl j) i
def SourceSink (k : V) : Prop :=
  (∀i,0≤B (Sum.inl k) i) ∨ (∀i,B (Sum.inl k) i≤0)

omit [Fintype V] [DecidableEq V] in
theorem diagonal (h : Skew B) (i : V) : B (Sum.inl i) i=0 := by
  have hh:=h i i
  omega

theorem principal (h : Skew B) (k : V) (hk : SourceSink B k) (i j : V) :
    matrix B k (Sum.inl i) j=if i=k ∨ j=k then -B (Sum.inl i) j else B (Sum.inl i) j := by
  rw [entry B k (diagonal B h k)]
  simp only [Sum.inl.injEq]
  split_ifs with hij
  · rfl
  · rcases hk with hs|hs
    · have hi : B (Sum.inl i) k≤0 := by rw [h i k];have:=hs i;omega
      have hj : -B (Sum.inl k) j≤0 := by have:=hs j;omega
      rw [max_eq_right hi,max_eq_right hj]
      ring
    · have hi : 0≤B (Sum.inl i) k := by rw [h i k];have:=hs i;omega
      have hj : 0≤ -B (Sum.inl k) j := by have:=hs j;omega
      rw [max_eq_left hi,max_eq_left hj]
      ring

theorem skew (h : Skew B) (k : V) (hk : SourceSink B k) : Skew (matrix B k) := by
  intro i j
  rw [principal B h k hk,principal B h k hk]
  by_cases hij : i=k ∨ j=k
  · rw [if_pos hij,if_pos (Or.comm.mp hij),h i j,neg_neg]
  · have hji : ¬(j=k ∨ i=k) := fun hh=>hij (Or.comm.mp hh)
    rw [if_neg hij,if_neg hji]
    exact h i j

theorem zero_iff (h : Skew B) (k : V) (hk : SourceSink B k) (i j : V) :
    matrix B k (Sum.inl i) j=0 ↔ B (Sum.inl i) j=0 := by
  rw [principal B h k hk]
  split_ifs <;> simp

theorem absolute (h : Skew B) (k : V) (hk : SourceSink B k) (i j : V) :
    |matrix B k (Sum.inl i) j|=|B (Sum.inl i) j| := by
  rw [principal B h k hk]
  split_ifs <;> simp

#print axioms Skew
#print axioms SourceSink
#print axioms diagonal
#print axioms principal
#print axioms skew
#print axioms zero_iff
#print axioms absolute
end Verification.RectangularSourceSinkMutation
