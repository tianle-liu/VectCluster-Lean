/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestEntries

/-!
# Path Forest Component Matrix

The actual finite principal matrix of the linearly oriented forest is
identified componentwise with the proved even/odd integral path operators.
-/

noncomputable section
namespace Verification.PathForestComponentMatrix
open Classical Verification.PathForestMatching Verification.PathForestFullRank Verification.PathForestEntries


def localPrincipal (m : ℕ) (o : Bool) :
    ((largeIndex m o → ℤ) × (Fin m → ℤ)) →ₗ[ℤ] ((largeIndex m o → ℤ) × (Fin m → ℤ)) :=
  match o with
  | false => PathLattice.evenOperator m
  | true => PathLattice.oddOperator m

theorem localPrincipal_formula (m : ℕ) (o : Bool) (p : largeIndex m o → ℤ) (q : Fin m → ℤ) :
    localPrincipal m o (p,q)=((localMatrix m o).mulVec q,-(localMatrix m o).transpose.mulVec p) := by
  cases o <;> rfl

variable {S : Type} [Fintype S] (m : S → ℕ) (o : S → Bool)
abbrev Vertices := PIndex m o ⊕ QIndex m

def components : (Vertices m o → ℤ) ≃ₗ[ℤ]
    ((s : S) → (largeIndex (m s) (o s) → ℤ) × (Fin (m s) → ℤ)) where
  toFun x s := (fun i=>x (Sum.inl ⟨s,i⟩),fun j=>x (Sum.inr ⟨s,j⟩))
  invFun x := Sum.elim (fun i=>(x i.1).1 i.2) (fun j=>(x j.1).2 j.2)
  left_inv x := by funext v;cases v <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev ordinaryMatrix := principal m o (fun _ _=>1) (fun _ _=>1)

theorem transpose_component (x : PIndex m o → ℤ) (s : S) (j : Fin (m s)) :
    (matchingMatrix m o (fun _ _=>1) (fun _ _=>1)).transpose.mulVec x ⟨s,j⟩=
      (localMatrix (m s) (o s)).transpose.mulVec (fun i=>x ⟨s,i⟩) j := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_sigma,Matrix.transpose_apply]
  rw [Finset.sum_eq_single s]
  · apply Finset.sum_congr rfl
    intro i _
    rw [same_component]
    simp
  · intro t _ hts
    apply Finset.sum_eq_zero
    intro i _
    rw [different_component m o (fun _ _=>1) (fun _ _=>1) t s hts]
    exact zero_mul _
  · simp

theorem principal_component (x : Vertices m o → ℤ) (s : S) :
    components m o ((ordinaryMatrix m o).mulVec x) s=
      localPrincipal (m s) (o s) (components m o x s) := by
  rw [ordinaryMatrix,principal,Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec,zero_add,add_zero,Matrix.neg_mulVec]
  rw [localPrincipal_formula]
  apply Prod.ext
  · funext i
    change (matchingMatrix m o (fun _ _=>1) (fun _ _=>1)).mulVec (fun j=>x (Sum.inr j)) ⟨s,i⟩=_
    have hm:=LinearMap.congr_fun (matchingMatrix_map m o (fun _ _=>1) (fun _ _=>1)) (fun j=>x (Sum.inr j))
    change (matchingMatrix m o (fun _ _=>1) (fun _ _=>1)).mulVec (fun j=>x (Sum.inr j))=_ at hm
    rw [hm]
    change (1:ℤ)*(localMatching (m s) (o s) (fun j=>1*x (Sum.inr ⟨s,j⟩))) i=_
    simp only [one_mul,← localMatrix_map]
    rfl
  · funext j
    change -((matchingMatrix m o (fun _ _=>1) (fun _ _=>1)).transpose.mulVec
      (fun i=>x (Sum.inl i)) ⟨s,j⟩) = _
    rw [transpose_component]
    rfl

#print axioms localPrincipal
#print axioms localPrincipal_formula
#print axioms Vertices
#print axioms components
#print axioms ordinaryMatrix
#print axioms transpose_component
#print axioms principal_component
end Verification.PathForestComponentMatrix
