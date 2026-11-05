/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathLattice
import Verification.PathPresentation

/-!
# Path Adjacency Monomials

Literal exchange monomials of the consecutive path matrix are exactly
the nearest-neighbour coordinates, with the endpoint value one.
-/
noncomputable section
namespace Verification.PathAdjacencyMonomials
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}

theorem positive_entry (r i : Fin n) : (PathLattice.pathMatrix n r i).toNat=
    if i.val=r.val+1 then 1 else 0 := by
  unfold PathLattice.pathMatrix
  split_ifs <;> omega

theorem negative_entry (r i : Fin n) : (-PathLattice.pathMatrix n r i).toNat=
    if r.val=i.val+1 then 1 else 0 := by
  unfold PathLattice.pathMatrix
  split_ifs <;> omega

def previous (x : Fin n → R) (i : Fin n) : R :=
  if h : 0 < i.val then x ⟨i.val-1,by omega⟩ else 1

def next (x : Fin n → R) (i : Fin n) : R :=
  if h : i.val+1<n then x ⟨i.val+1,h⟩ else 1

theorem positive_product (x : Fin n → R) (i : Fin n) :
    (∏ r,x r^(PathLattice.pathMatrix n r i).toNat)=previous x i := by
  classical
  simp only [positive_entry]
  by_cases h : 0 < i.val
  · let j : Fin n := ⟨i.val-1,by omega⟩
    rw [Finset.prod_eq_single j]
    · rw [previous,dif_pos h,if_pos (show i.val=j.val+1 by dsimp [j];omega),pow_one]
    · intro r _ hr
      have hi : i.val≠r.val+1 := by
        intro he
        apply hr
        apply Fin.ext
        dsimp [j]
        omega
      simp [hi]
    · simp
  · rw [Finset.prod_eq_one]
    · simp [previous,h]
    · intro r _
      have hi : i.val≠r.val+1 := by omega
      simp [hi]

theorem negative_product (x : Fin n → R) (i : Fin n) :
    (∏ r,x r^(-PathLattice.pathMatrix n r i).toNat)=next x i := by
  classical
  simp only [negative_entry]
  by_cases h : i.val+1<n
  · let j : Fin n := ⟨i.val+1,h⟩
    rw [Finset.prod_eq_single j]
    · simp [next,h,j]
    · intro r _ hr
      have hi : r.val≠i.val+1 := by
        intro he
        apply hr
        exact Fin.ext he
      simp [hi]
    · simp
  · rw [Finset.prod_eq_one]
    · simp [next,h]
    · intro r _
      have hi : r.val≠i.val+1 := by omega
      simp [hi]

theorem previous_boundary (x : Fin n → R) (i : Fin n) :
    previous x i=PathPresentation.boundary 1 1 x i.castSucc.castSucc := by
  by_cases h : 0 < i.val
  · let j : Fin n := ⟨i.val-1,by omega⟩
    have hi : i.castSucc.castSucc=j.castSucc.succ := by
      apply Fin.ext
      dsimp [j]
      omega
    rw [hi,PathPresentation.boundary_middle]
    simp [previous,h,j]
  · have hi : i.castSucc.castSucc=0 := by apply Fin.ext;dsimp;omega
    rw [hi,PathPresentation.boundary_zero]
    simp [previous,h]

theorem next_boundary (x : Fin n → R) (i : Fin n) :
    next x i=PathPresentation.boundary 1 1 x i.succ.succ := by
  by_cases h : i.val+1<n
  · let j : Fin n := ⟨i.val+1,h⟩
    have hi : i.succ.succ=j.castSucc.succ := by apply Fin.ext;rfl
    rw [hi,PathPresentation.boundary_middle]
    simp [next,h,j]
  · have hi : i.succ.succ=Fin.last (n+1) := by apply Fin.ext;dsimp;omega
    rw [hi,PathPresentation.boundary_last]
    simp [next,h]

theorem exchange_equations (x y : Fin n → R) :
    (∀ i,x i*y i=(∏ r,x r^(PathLattice.pathMatrix n r i).toNat)+
      ∏ r,x r^(-PathLattice.pathMatrix n r i).toNat) ↔ PathPresentation.Equations 1 1 x y := by
  simp only [positive_product,negative_product,previous_boundary,next_boundary,PathPresentation.Equations]

#print axioms positive_entry
#print axioms negative_entry
#print axioms previous
#print axioms next
#print axioms positive_product
#print axioms negative_product
#print axioms previous_boundary
#print axioms next_boundary
#print axioms exchange_equations
end Verification.PathAdjacencyMonomials
