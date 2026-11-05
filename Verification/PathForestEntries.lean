/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestFullRank
import Verification.PathOrientationSigns

/-!
# Path Forest Entries

Entrywise identification of the actual forest matching matrix. The
matrix has only the two adjacent entries on each component, and arbitrary
single-arrow orientations are exactly the cumulative vertex signs.
-/

noncomputable section
namespace Verification.PathForestEntries
open Classical Verification.PathForestMatching Verification.PathForestFullRank


def localMatrix (m : ℕ) (o : Bool) : Matrix (largeIndex m o) (Fin m) ℤ :=
  match o with
  | false => PathLattice.bidiagonal m
  | true => PathLattice.difference m

theorem localMatrix_map (m : ℕ) (o : Bool) : (localMatrix m o).mulVecLin=localMatching m o := by
  cases o <;> rfl

variable {S : Type} [Fintype S] (m : S → ℕ) (o : S → Bool)
variable (u : (s : S) → largeIndex (m s) (o s) → ℤˣ) (v : (s : S) → Fin (m s) → ℤˣ)

theorem same_component (s : S) (i : largeIndex (m s) (o s)) (j : Fin (m s)) :
    matchingMatrix m o u v ⟨s,i⟩ ⟨s,j⟩=(u s i:ℤ)*localMatrix (m s) (o s) i j*(v s j:ℤ) := by
  change (u s i:ℤ)*(localMatching (m s) (o s)
    (fun k=>(v s k:ℤ)*(Pi.single (⟨s,j⟩ : QIndex m) (1:ℤ) : QIndex m → ℤ) ⟨s,k⟩)) i=_
  have h : (fun k=>(v s k:ℤ)*(Pi.single (⟨s,j⟩ : QIndex m) (1:ℤ) : QIndex m → ℤ) ⟨s,k⟩)=Pi.single j (v s j:ℤ) := by
    funext k
    by_cases hk : k=j
    · subst k;simp
    · have he : (⟨s,k⟩ : QIndex m)≠⟨s,j⟩ := by intro h;cases h;exact hk rfl
      simp [Pi.single_apply,hk,he]
  rw [h,← localMatrix_map]
  change (u s i:ℤ)*((localMatrix (m s) (o s)).mulVec (Pi.single j (v s j:ℤ))) i=_
  rw [Matrix.mulVec_single]
  change _*(_*_)=_*_*_
  exact (mul_assoc _ _ _).symm

theorem different_component (s t : S) (hst : s≠t)
    (i : largeIndex (m s) (o s)) (j : Fin (m t)) :
    matchingMatrix m o u v ⟨s,i⟩ ⟨t,j⟩=0 := by
  change (u s i:ℤ)*(localMatching (m s) (o s)
    (fun k=>(v s k:ℤ)*(Pi.single (⟨t,j⟩ : QIndex m) (1:ℤ) : QIndex m → ℤ) ⟨s,k⟩)) i=0
  have h : (fun k=>(v s k:ℤ)*(Pi.single (⟨t,j⟩ : QIndex m) (1:ℤ) : QIndex m → ℤ) ⟨s,k⟩)=0 := by
    funext k
    have he : (⟨s,k⟩ : QIndex m)≠⟨t,j⟩ := by intro h;exact hst (congrArg Sigma.fst h)
    simp [Pi.single_apply,he]
  rw [h,map_zero]
  exact mul_zero _

#print axioms localMatrix
#print axioms localMatrix_map
#print axioms same_component
#print axioms different_component
end Verification.PathForestEntries
