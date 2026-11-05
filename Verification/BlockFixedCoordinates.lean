/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathConeBlocks
import Verification.PerturbedHomologyModel

/-!
# Block Fixed Coordinates

Actual degreewise fixed modules of a block-diagonal projector split into
the two fixed modules, with no freeness or dimension assumption.
-/

namespace Verification.BlockFixedCoordinates

open Verification.GradedPerturbation Verification.PerturbedHomologyModel
  Verification.PathConeBlocks

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def coordinates (a : ι → ℤ) (b : κ → ℤ) (P : Matrix ι ι R) (Q : Matrix κ κ R) (p : ℤ) :
    fixedModule (Sum.elim a b) (diagonal P Q) p ≃ₗ[R] (fixedModule a P p × fixedModule b Q p) where
  toFun x := (⟨fun i => x.val (Sum.inl i),
    (fun i hi => x.property.1 (Sum.inl i) hi),by
      have hh := congrArg (fun f : ι ⊕ κ → R => fun i => f (Sum.inl i)) x.property.2
      simpa only [diagonal,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,add_zero,Sum.elim_inl] using hh⟩,
    ⟨fun j => x.val (Sum.inr j),
    (fun j hj => x.property.1 (Sum.inr j) hj),by
      have hh := congrArg (fun f : ι ⊕ κ → R => fun j => f (Sum.inr j)) x.property.2
      simpa only [diagonal,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,zero_add,Sum.elim_inr] using hh⟩)
  invFun x := ⟨Sum.elim x.1.val x.2.val,by
    constructor
    · intro i hi
      cases i with
      | inl i => exact x.1.property.1 i hi
      | inr i => exact x.2.property.1 i hi
    · rw [diagonal,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,Matrix.zero_mulVec,add_zero,zero_add]
      change Sum.elim (P.mulVec x.1.val) (Q.mulVec x.2.val)=Sum.elim x.1.val x.2.val
      rw [x.1.property.2,x.2.property.2]⟩
  left_inv x := by apply Subtype.ext; funext i; cases i <;> rfl
  right_inv x := by apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' x y := by apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' r x := by apply Prod.ext <;> apply Subtype.ext <;> rfl

omit [Fintype κ] in
noncomputable def shift (a : ι → ℤ) (P : Matrix ι ι R) (p t : ℤ) :
    fixedModule (fun i => a i+t) P p ≃ₗ[R] fixedModule a P (p-t) :=
  LinearEquiv.ofEq _ _ (by
    apply Submodule.ext
    intro x
    change ((∀ i,a i+t ≠ p → x i=0) ∧ _) ↔ ((∀ i,a i ≠ p-t → x i=0) ∧ _)
    constructor
    · rintro ⟨hx,hp⟩
      exact ⟨fun i hi => hx i (by omega),hp⟩
    · rintro ⟨hx,hp⟩
      exact ⟨fun i hi => hx i (by omega),hp⟩)

omit [Fintype κ] in
theorem fixed_zero (a : ι → ℤ) (P : Matrix ι ι R)
    (hP : ∀ i j,a i ≠ 0 → P i j=0) (p : ℤ) (hp : p ≠ 0)
    (x : fixedModule a P p) : x=0 := by
  apply Subtype.ext
  funext i
  by_cases hi : a i=p
  · have hh := congrFun x.property.2 i
    change (∑ j,P i j*x.val j)=x.val i at hh
    have hz : (∑ j,P i j*x.val j)=0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hP i j (by omega),zero_mul]
    exact hh.symm.trans hz
  · exact x.property.1 i hi

#print axioms coordinates
#print axioms shift
#print axioms fixed_zero

end Verification.BlockFixedCoordinates
