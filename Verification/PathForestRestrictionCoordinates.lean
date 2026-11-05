/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SelectedPathIntervals
import Verification.PathForestMatrixPredicate
import Mathlib.Logic.Equiv.Set

/-!
# Path Forest Restriction Coordinates

The explicit interval coordinates of every principal restriction of a
signed path forest. The component lengths and edge signs are constructed.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Verification.PathForestRestrictionCoordinates
open Classical Verification.PathForestOrientation Verification.SelectedPathIntervals
variable {S : Type} (m : S→ℕ) (o : S→Bool)
variable {k : ℕ} (f : Fin k↪Vertex m o)

def selected (s : S) : Set (Fin (PathOrientationBlocks.length (m s) (o s))) :=
  fun i=>⟨s,i⟩∈Set.range f
abbrev Index := Σs,Component (selected m o f s)
def size (c : Index m o f) : ℕ := Fintype.card (Points (selected m o f c.1) c.2)
def halves (c : Index m o f) : ℕ := size m o f c/2
def odd (c : Index m o f) : Bool := decide (size m o f c%2=1)

theorem length_eq (c : Index m o f) :
    PathOrientationBlocks.length (halves m o f c) (odd m o f c)=size m o f c := by
  unfold halves odd
  by_cases h : size m o f c%2=1
  · simp only [h,decide_true,PathOrientationBlocks.length]
    omega
  · simp only [h,decide_false,PathOrientationBlocks.length]
    omega

def enumerate (c : Index m o f) :
    Fin (PathOrientationBlocks.length (halves m o f c) (odd m o f c))≃Points (selected m o f c.1) c.2 :=
  (finCongr (length_eq m o f c)).trans (ordering (selected m o f c.1) c.2).toEquiv

def selectedEquiv : (Σs,selected m o f s)≃Set.range f where
  toFun x:=⟨⟨x.1,x.2.val⟩,x.2.property⟩
  invFun x:=⟨x.val.1,⟨x.val.2,x.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

def reindex : Vertex (halves m o f) (odd m o f)≃Fin k :=
  (Equiv.sigmaCongrRight (enumerate m o f)).trans
    ((Equiv.sigmaAssoc (fun s c=>Points (selected m o f s) c)).trans
      ((Equiv.sigmaCongrRight (fun s=>split (selected m o f s))).trans
        ((selectedEquiv m o f).trans (Equiv.ofInjective f f.injective).symm)))

theorem reindex_apply (c : Index m o f)
    (i : Fin (PathOrientationBlocks.length (halves m o f c) (odd m o f c))) :
    f (reindex m o f ⟨c,i⟩)=⟨c.1,(enumerate m o f c i).val⟩ :=
  Equiv.apply_ofInjective_symm f.injective _

theorem consecutive (c : Index m o f)
    (i j : Fin (PathOrientationBlocks.length (halves m o f c) (odd m o f c))) :
    (enumerate m o f c j).val.val=(enumerate m o f c i).val.val+1 ↔ j.val=i.val+1 :=
  SelectedPathIntervals.consecutive (selected m o f c.1) c.2
    (finCongr (length_eq m o f c) i) (finCongr (length_eq m o f c) j)

variable (a : S→ℕ→ℤˣ)
def signs (c : Index m o f) (t : ℕ) : ℤˣ :=
  if h : t<PathOrientationBlocks.length (halves m o f c) (odd m o f c)
    then a c.1 (enumerate m o f c ⟨t,h⟩).val.val else 1

theorem signs_apply (c : Index m o f)
    (i : Fin (PathOrientationBlocks.length (halves m o f c) (odd m o f c))) :
    signs m o f a c i.val=a c.1 (enumerate m o f c i).val.val := by
  simp only [signs,dif_pos i.isLt]

theorem local_matrix (c : Index m o f)
    (i j : Fin (PathOrientationBlocks.length (halves m o f c) (odd m o f c))) :
    PathOrientationSigns.matrix (a c.1) _ (enumerate m o f c i).val (enumerate m o f c j).val=
      PathOrientationSigns.matrix (signs m o f a c) _ i j := by
  simp only [PathOrientationSigns.matrix,consecutive,signs_apply]

#print axioms selected
#print axioms Index
#print axioms size
#print axioms halves
#print axioms odd
#print axioms length_eq
#print axioms enumerate
#print axioms selectedEquiv
#print axioms reindex
#print axioms reindex_apply
#print axioms consecutive
#print axioms signs
#print axioms signs_apply
#print axioms local_matrix
end Verification.PathForestRestrictionCoordinates
