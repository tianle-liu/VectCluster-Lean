/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FlagNormalCoordinates
import Verification.NormalFrameInsertion

/-!
# Ordered Flag Normal Coordinates

Identify the literal new-first normal coordinate equivalence with
an increasing-coordinate equivalence followed by the actual insertion
permutation. The coefficient quotient map is retained throughout.
-/
noncomputable section
namespace Verification.OrderedFlagNormalCoordinates
open Verification.NormalFrameInsertion
variable (ι : Type) [Fintype ι] [LinearOrder ι] (v : ι)

abbrev oldSet : Finset ι := Finset.univ.erase v
abbrev count : ℕ := (oldSet ι v).card + 1

def increasing : Fin (count ι v) ≃ ι :=
  Equiv.ofBijective (newFrame (oldSet ι v) v (by simp [oldSet])) ⟨
    (newFrame (oldSet ι v) v (by simp [oldSet])).injective, by
    intro i
    let q := ((insert v (oldSet ι v)).orderIsoOfFin
      (Finset.card_insert_of_not_mem (by simp [oldSet]))).symm ⟨i,by simp [oldSet]⟩
    exact ⟨q,congrArg Subtype.val (((insert v (oldSet ι v)).orderIsoOfFin
      (Finset.card_insert_of_not_mem (by simp [oldSet]))).apply_symm_apply ⟨i,by simp [oldSet]⟩)⟩⟩

def insertion : Equiv.Perm (Fin (count ι v)) :=
  permutation (oldSet ι v) v (by simp [oldSet])

def newFirst : Fin (count ι v) ≃ ι := (insertion ι v).symm.trans (increasing ι v)

theorem newFirst_apply (q : Fin (count ι v)) :
    newFirst ι v q = (Fin.cons v (fun j => (oldSet ι v).orderEmbOfFin rfl j) : Fin (count ι v) → ι) q := by
  have h := congrFun (frame_reordering (oldSet ι v) v (by simp [oldSet])) ((insertion ι v).symm q)
  change newFrame (oldSet ι v) v (by simp [oldSet]) ((insertion ι v).symm q) = _
  simpa only [Function.comp_apply,insertion,Equiv.apply_symm_apply] using h.symm

def normalOrder : Fin (count ι v) ≃ FlagNormalCoordinates.Normals ι v :=
  (newFirst ι v).trans (FlagNormalCoordinates.indexEquiv ι v).symm

theorem normalOrder_new : normalOrder ι v 0 = none := by
  apply (FlagNormalCoordinates.indexEquiv ι v).injective
  simp only [normalOrder,Equiv.trans_apply,Equiv.apply_symm_apply,newFirst_apply,Fin.cons_zero,
    FlagNormalCoordinates.indexEquiv_new]

theorem normalOrder_old (q : Fin (oldSet ι v).card) :
    normalOrder ι v q.succ = some (⟨(oldSet ι v).orderEmbOfFin rfl q,
      Finset.ne_of_mem_erase ((oldSet ι v).orderEmbOfFin_mem rfl q)⟩ : CoordinateFlag.Old ι v) := by
  apply (FlagNormalCoordinates.indexEquiv ι v).injective
  simp only [normalOrder,Equiv.trans_apply,Equiv.apply_symm_apply,newFirst_apply,Fin.cons_succ,
    FlagNormalCoordinates.indexEquiv_old]

theorem newFirst_inverse (i : ι) :
    (newFirst ι v).symm i = insertion ι v ((increasing ι v).symm i) := rfl

theorem insertion_sign : Equiv.Perm.sign (insertion ι v) =
    (-1) ^ ((oldSet ι v).filter (fun i => i < v)).card :=
  permutation_sign (oldSet ι v) v (by simp [oldSet])

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (x : ι → A)

def orderedEquiv : MvPolynomial ι (A ⧸ ConormalFrame.ideal x) ≃ₐ[R]
    MvPolynomial (Fin (count ι v)) (CoordinateFlag.ClosedAll A ι x v) :=
  (MvPolynomial.mapAlgEquiv ι (CoordinateFlagTotalQuotient.equiv R A ι x v).symm).trans
    ((MvPolynomial.renameEquiv (CoordinateFlag.ClosedAll A ι x v) (increasing ι v).symm).restrictScalars R)

def normalNumbering : MvPolynomial (FlagNormalCoordinates.Normals ι v) (CoordinateFlag.ClosedAll A ι x v) ≃ₐ[R]
    MvPolynomial (Fin (count ι v)) (CoordinateFlag.ClosedAll A ι x v) :=
  (MvPolynomial.renameEquiv (CoordinateFlag.ClosedAll A ι x v) (normalOrder ι v).symm).restrictScalars R

def insertionEquiv : MvPolynomial (Fin (count ι v)) (CoordinateFlag.ClosedAll A ι x v) ≃ₐ[R]
    MvPolynomial (Fin (count ι v)) (CoordinateFlag.ClosedAll A ι x v) :=
  (MvPolynomial.renameEquiv (CoordinateFlag.ClosedAll A ι x v) (insertion ι v)).restrictScalars R

theorem algebra_factorization :
    (FlagNormalCoordinates.algebraEquiv R A ι x v).trans (normalNumbering ι v R A x) =
      (orderedEquiv ι v R A x).trans (insertionEquiv ι v R A x) := by
  apply AlgEquiv.coe_algHom_injective
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [FlagNormalCoordinates.algebraEquiv,normalNumbering,orderedEquiv,insertionEquiv,
      MvPolynomial.mapAlgEquiv_apply,MvPolynomial.renameEquiv_apply]
  · intro i
    change normalNumbering ι v R A x (FlagNormalCoordinates.algebraEquiv R A ι x v (MvPolynomial.X i)) =
      insertionEquiv ι v R A x (orderedEquiv ι v R A x (MvPolynomial.X i))
    simp [FlagNormalCoordinates.algebraEquiv,normalNumbering,orderedEquiv,insertionEquiv,
      MvPolynomial.mapAlgEquiv_apply,MvPolynomial.renameEquiv_apply,normalOrder,newFirst]

#print axioms oldSet
#print axioms count
#print axioms increasing
#print axioms insertion
#print axioms newFirst
#print axioms newFirst_apply
#print axioms normalOrder
#print axioms normalOrder_new
#print axioms normalOrder_old
#print axioms newFirst_inverse
#print axioms insertion_sign
#print axioms orderedEquiv
#print axioms normalNumbering
#print axioms insertionEquiv
#print axioms algebra_factorization
end Verification.OrderedFlagNormalCoordinates
