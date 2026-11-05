/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PositiveGradedContraction
import Verification.BiprodHomotopyEquiv
import Mathlib.Algebra.Homology.Single

/-!
# Graded Coefficient Realization

A homogeneous positive-weight contraction realizes as an actual homotopy
of K_j-valued complexes. The independent constant Z[0] is added by biproduct;
no action on Z, exact tensor functor, or projectivity assertion is used.
-/

noncomputable section
namespace Verification.GradedCoefficientRealization

open Classical CategoryTheory CategoryTheory.Limits
  Verification.GradedCoefficientCategory Verification.GradedMatrixComplex

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasZeroObject C] [HasBinaryBiproducts C]
variable (K : ℕ → C) (A : PathGradedCoefficientAction.Action (fun j=>K (j+1)))
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {w : ι → ℕ} {v : κ → ℕ} {d : ι → ℤ} (T : PositiveGradedContraction.Data w v d)

abbrev sourceIndex (w : ι → ℕ) (d : ι → ℤ) (p : ℤ) := {i : {i // 0<w i} // d i.val=p}
abbrev targetIndex (v : κ → ℕ) (p : ℤ) := {_k : {k // 0<v k} // (0:ℤ)=p}

def source : CochainComplex C ℤ :=
  ((positiveRealization K A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (complex (PositiveGradedContraction.positiveSpace w) (fun i=>d i.val)
      (PositiveGradedContraction.differential T) (PositiveGradedContraction.differential_supported T)
      (PositiveGradedContraction.differential_square T))

def target : CochainComplex C ℤ :=
  ((positiveRealization K A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (complex (PositiveGradedContraction.positiveSpace v) (fun _=>0) 0 (supported_zero _ _ 1) (by simp))

def equivalence : HomotopyEquiv (source K A T) (target K A (v:=v)) :=
  (positiveRealization K A).mapHomotopyEquiv (PositiveGradedContraction.equivalence T)

def sourceTermIso (p : ℤ) : (source K A T).X p ≅
    ⨁ fun i : sourceIndex w d p=>K (w i.val.val) := by
  change (⨁ fun i : sourceIndex w d p=>K (w i.val.val-1+1)) ≅ _
  exact biproduct.mapIso (fun i=>eqToIso (congrArg K (Nat.sub_add_cancel (by have h:=i.val.property;omega))))

def survivorObject (v : κ → ℕ) : C := ⨁ fun k : {k // 0<v k}=>K (v k.val)

def removeZeroDegree (v : κ → ℕ) : targetIndex v 0 ≃ {k // 0<v k} where
  toFun := Subtype.val
  invFun k := ⟨k,rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

def targetZeroIso : (target K A (v:=v)).X 0 ≅ survivorObject K v := by
  change (⨁ fun k : targetIndex v 0=>K (v k.val.val-1+1)) ≅ _
  exact (biproduct.mapIso (fun k=>eqToIso
    (congrArg K (Nat.sub_add_cancel (by have h:=k.val.property;omega))))) ≪≫
      biproduct.reindex (removeZeroDegree v) (fun k=>K (v k.val))

omit [HasZeroObject C] [HasBinaryBiproducts C] in
theorem targetTermZero (p : ℤ) (hp : p≠0) : IsZero ((target K A (v:=v)).X p) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  change (𝟙 (⨁ fun k : targetIndex v p=>K (v k.val.val-1+1)))=0
  apply biproduct.hom_ext
  intro k
  exact (hp k.property.symm).elim

omit [HasZeroObject C] [HasBinaryBiproducts C] in
theorem target_d (p q : ℤ) : (target K A (v:=v)).d p q=0 := by
  change (positiveRealization K A).map ((complex (PositiveGradedContraction.positiveSpace v)
    (fun _=>0) 0 (supported_zero _ _ 1) (by simp)).d p q)=0
  by_cases h : p+1=q
  · rw [complex_d_between _ _ _ _ _ p q h,cut_zero,Functor.map_zero]
  · rw [HomologicalComplex.shape _ p q h,Functor.map_zero]

def targetSingleIso : target K A (v:=v) ≅
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (survivorObject K v) :=
  HomologicalComplex.Hom.isoOfComponents (fun p=>by
    by_cases hp : p=0
    · subst p
      exact targetZeroIso K A ≪≫ (HomologicalComplex.singleObjXSelf _ 0 _).symm
    · exact (targetTermZero K A p hp).iso
        (HomologicalComplex.isZero_single_obj_X _ 0 _ p hp)) (by
      intro p q _
      rw [target_d,HomologicalComplex.single_obj_d,comp_zero,zero_comp])

def positiveEquivalence : HomotopyEquiv (source K A T)
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (survivorObject K v)) :=
  (equivalence K A T).trans (HomotopyEquiv.ofIso (targetSingleIso K A))

def withConstant (Z : C) : CochainComplex C ℤ :=
  (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z ⊞ source K A T

/-- Literal Z ⊕ positive MW terms, concentrated in degree zero. -/
def fullEquivalence (Z : C) : HomotopyEquiv (withConstant K A T Z)
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (Z ⊞ survivorObject K v)) := by
  letI : PreservesBinaryBiproducts (HomologicalComplex.single C (ComplexShape.up ℤ) 0) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact (BiprodHomotopyEquiv.equivalence ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z)
    (positiveEquivalence K A T)).trans
      (HomotopyEquiv.ofIso ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).mapBiprod Z
        (survivorObject K v)).symm)

#print axioms sourceIndex
#print axioms targetIndex
#print axioms source
#print axioms target
#print axioms equivalence
#print axioms sourceTermIso
#print axioms survivorObject
#print axioms removeZeroDegree
#print axioms targetZeroIso
#print axioms targetTermZero
#print axioms target_d
#print axioms targetSingleIso
#print axioms positiveEquivalence
#print axioms withConstant
#print axioms fullEquivalence

end Verification.GradedCoefficientRealization
