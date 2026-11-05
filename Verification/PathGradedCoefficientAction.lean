/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathGradedMatrices
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Path Graded Coefficient Action

Realization of graded path coefficients in an arbitrary preadditive
category with finite biproducts. An action is only the usual graded additive
module action; it contains no path differential, vanishing or comparison
assumption. This is a generic coefficient action. The sheaf application
uses a separate constant Z summand and the positive-weight construction
in PathGradedSheafModel; it does not equip Z with a Milnor--Witt action.
No projectivity, flatness, or exactness of tensoring is required.
-/

noncomputable section
namespace Verification.PathGradedCoefficientAction

open CategoryTheory CategoryTheory.Limits Verification.PathCoefficientRing

/-- Actual homogeneous elements of the quotient coefficient ring. -/
def piece (k : ℤ) : AddSubgroup Coeff where
  carrier := {r | PathCoefficientGrading.Homogeneous k r}
  zero_mem' := PathCoefficientGrading.homogeneous_zero k
  add_mem' := PathCoefficientGrading.homogeneous_add
  neg_mem' := PathCoefficientGrading.homogeneous_neg

def product {i j k : ℕ} (b : piece ((k:ℤ)-j)) (a : piece ((j:ℤ)-i)) : piece ((k:ℤ)-i) :=
  ⟨b.val*a.val,by
    change PathCoefficientGrading.Homogeneous ((k:ℤ)-i) (b.val*a.val)
    convert PathCoefficientGrading.homogeneous_mul b.property a.property using 1
    omega⟩

def unit (i : ℕ) : piece ((i:ℤ)-i) :=
  ⟨1,by simpa only [sub_self] using PathCoefficientGrading.homogeneous_one⟩

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] (K : ℕ → C)

/-- The standard graded coefficient-module axioms, independent of paths. -/
structure Action where
  act : ∀ i j : ℕ,piece ((j:ℤ)-i) →+ (K i ⟶ K j)
  one : ∀ i,act i i (unit i)=𝟙 (K i)
  mul : ∀ (i j k : ℕ) (b : piece ((k:ℤ)-j)) (a : piece ((j:ℤ)-i)),
    act i k (product b a)=act i j a ≫ act j k b

variable [HasFiniteBiproducts C] (T : Action K)
variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

/-- A literal weighted matrix acts between the indicated sums of K_j. -/
def realize (target : ι → ℕ) (source : κ → ℕ) (M : Matrix ι κ Coeff)
    (hM : PathGradedMatrices.Homogeneous (fun i=>(target i:ℤ)) (fun j=>(source j:ℤ)) M) :
    (⨁ fun j=>K (source j)) ⟶ ⨁ fun i=>K (target i) :=
  biproduct.matrix (fun j i=>T.act (source j) (target i) ⟨M i j,hM i j⟩)

theorem component (target : ι → ℕ) (source : κ → ℕ) (M : Matrix ι κ Coeff)
    (hM : PathGradedMatrices.Homogeneous (fun i=>(target i:ℤ)) (fun j=>(source j:ℤ)) M)
    (j : κ) (i : ι) :
    biproduct.ι (fun j=>K (source j)) j ≫ realize K T target source M hM ≫
      biproduct.π (fun i=>K (target i)) i=T.act (source j) (target i) ⟨M i j,hM i j⟩ := by
  simp [realize]

theorem realize_zero (target : ι → ℕ) (source : κ → ℕ) :
    realize K T target source 0 (PathGradedMatrices.zero _ _)=0 := by
  apply biproduct.hom_ext
  intro i
  apply biproduct.hom_ext'
  intro j
  simp only [Category.assoc,component,comp_zero,zero_comp]
  exact map_zero (T.act (source j) (target i))

theorem realize_add (target : ι → ℕ) (source : κ → ℕ) (M N : Matrix ι κ Coeff)
    (hM : PathGradedMatrices.Homogeneous (fun i=>(target i:ℤ)) (fun j=>(source j:ℤ)) M)
    (hN : PathGradedMatrices.Homogeneous (fun i=>(target i:ℤ)) (fun j=>(source j:ℤ)) N) :
    realize K T target source (M+N) (PathGradedMatrices.add _ _ M N hM hN)=
      realize K T target source M hM+realize K T target source N hN := by
  apply biproduct.hom_ext
  intro i
  apply biproduct.hom_ext'
  intro j
  simp only [Preadditive.add_comp,Preadditive.comp_add,Category.assoc,component]
  exact map_add (T.act (source j) (target i)) ⟨M i j,hM i j⟩ ⟨N i j,hN i j⟩

theorem realize_mul (target : ι → ℕ) (middle : κ → ℕ) (source : ν → ℕ)
    (M : Matrix ι κ Coeff) (N : Matrix κ ν Coeff)
    (hM : PathGradedMatrices.Homogeneous (fun i=>(target i:ℤ)) (fun j=>(middle j:ℤ)) M)
    (hN : PathGradedMatrices.Homogeneous (fun j=>(middle j:ℤ)) (fun k=>(source k:ℤ)) N) :
    realize K T target source (M*N) (PathGradedMatrices.mul _ _ _ M N hM hN)=
      realize K T middle source N hN ≫ realize K T target middle M hM := by
  apply biproduct.hom_ext
  intro i
  apply biproduct.hom_ext'
  intro k
  simp only [Category.assoc,component]
  simp only [realize,biproduct.ι_matrix_assoc,biproduct.matrix_π,biproduct.lift_desc]
  have he : (⟨(M*N) i k,(PathGradedMatrices.mul _ _ _ M N hM hN) i k⟩ : piece ((target i:ℤ)-source k))=
      ∑ j,product (⟨M i j,hM i j⟩ : piece ((target i:ℤ)-middle j))
        (⟨N j k,hN j k⟩ : piece ((middle j:ℤ)-source k)) := by
    apply Subtype.ext
    change (M*N) i k=(piece ((target i:ℤ)-source k)).subtype (∑ j,
      product (⟨M i j,hM i j⟩ : piece ((target i:ℤ)-middle j))
        (⟨N j k,hN j k⟩ : piece ((middle j:ℤ)-source k)))
    rw [map_sum]
    rfl
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact T.mul (source k) (middle j) (target i) _ _

theorem realize_one [DecidableEq ι] (weight : ι → ℕ) :
    realize K T weight weight 1 (PathGradedMatrices.one _)=𝟙 _ := by
  apply biproduct.hom_ext
  intro i
  apply biproduct.hom_ext'
  intro j
  simp only [Category.assoc,component,Category.id_comp]
  by_cases he : j=i
  · subst j
    simpa only [Matrix.one_apply_eq,biproduct.ι_π_self] using T.one (weight i)
  · rw [biproduct.ι_π_ne _ he]
    have hij : i≠j := Ne.symm he
    simp only [Matrix.one_apply_ne hij]
    exact map_zero (T.act (weight j) (weight i))

#print axioms piece
#print axioms product
#print axioms unit
#print axioms Action
#print axioms realize
#print axioms component
#print axioms realize_zero
#print axioms realize_add
#print axioms realize_mul
#print axioms realize_one

end Verification.PathGradedCoefficientAction
