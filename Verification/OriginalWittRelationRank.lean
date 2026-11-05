/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittQuotient
import Verification.IntegerLinearReduction
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Original Witt Relation Rank

Independence modulo two of the manuscript's actual e_i and b_i.
The selected columns have an integral retraction by AS, which is reduced
modulo two; the deleted normal coordinates detect the remaining coefficients.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalWittRelationRank
open Verification.OriginalWittQuotient Verification.AnticliqueSubcolumns
variable {V C : Type*} [Fintype V] [Fintype C]

def relationMap (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    ((I ⊕ I) → ZMod 2) →ₗ[ZMod 2] Bits V C := by
  classical
  exact Matrix.toLin' (fun a s => Multiplicative.toAdd (generator B I s) a)

omit [Fintype V] [Fintype C] in
theorem relationMap_apply (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (x : (I ⊕ I) → ZMod 2) (a : V ⊕ C) :
    relationMap B I x a =
      (∑ i : I, (Pi.single (Sum.inl i.val) (1:ZMod 2) : Bits V C) a * x (Sum.inl i)) +
      ∑ i : I, (B a i.val : ZMod 2) * x (Sum.inr i) := by
  classical
  simp [relationMap,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
    generator,normalVector,columnVector]

omit [Fintype V] [Fintype C] in
theorem normal_coordinate (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hz : ∀ i j : I, B (Sum.inl j.val) i.val = 0)
    (x : (I ⊕ I) → ZMod 2) (j : I) :
    relationMap B I x (Sum.inl j.val) = x (Sum.inl j) := by
  classical
  rw [relationMap_apply]
  simp [hz,Pi.single_apply,Subtype.val_inj]

theorem remaining_coordinate (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (x : (I ⊕ I) → ZMod 2) (a : Rows (C := C) I) :
    relationMap B I x a.val =
      Verification.IntegerLinearReduction.reduce (selectedMap B I) (x ∘ Sum.inr) a := by
  classical
  rw [relationMap_apply,Verification.IntegerLinearReduction.reduce_apply]
  have hz (i : I) : (Pi.single (Sum.inl i.val) (1:ZMod 2) : Bits V C) a.val = 0 := by
    exact Pi.single_eq_of_ne (a.property i.val i.property) 1
  simp [hz,selectedMap,column,Finsupp.linearCombination_single]

theorem relationMap_injective (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hz : ∀ i j : I, B (Sum.inl j.val) i.val = 0) (hAS : AS B I) :
    Function.Injective (relationMap B I) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hn (i : I) : x (Sum.inl i) = 0 := by
    rw [← normal_coordinate B I hz x i,hx]
    rfl
  have hr : Verification.IntegerLinearReduction.reduce (selectedMap B I) (x ∘ Sum.inr) = 0 := by
    funext a
    rw [← remaining_coordinate B I x a,hx]
    rfl
  have hi := Verification.IntegerLinearReduction.injective_of_primitive
    (selectedMap B I) hAS.1 hAS.2
  have hb : x ∘ Sum.inr = 0 := hi (hr.trans (map_zero _).symm)
  funext i
  cases i with
  | inl i => exact hn i
  | inr i => exact congrFun hb i

omit [Fintype V] [Fintype C] in
theorem relationMap_single (B : (V ⊕ C) → V → ℤ) (I : Finset V) (i : I ⊕ I) :
    relationMap B I (Pi.single i 1) = Multiplicative.toAdd (generator B I i) := by
  classical
  simp only [relationMap,Matrix.toLin'_apply,Matrix.mulVec_single,MulOpposite.op_one,one_smul]
  rfl

theorem quotient_dimension (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hz : ∀ i j : I, B (Sum.inl j.val) i.val = 0) (hAS : AS B I) :
    Module.finrank (ZMod 2) (Bits V C ⧸ LinearMap.range (relationMap B I)) =
      Fintype.card V + Fintype.card C - 2*I.card := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (relationMap B I))
  have e := (LinearEquiv.ofInjective (relationMap B I) (relationMap_injective B I hz hAS)).finrank_eq
  simp only [Module.finrank_pi,Fintype.card_sum,Module.finrank_self,mul_one,
    Fintype.card_coe] at h e
  change Module.finrank (ZMod 2) (Bits V C ⧸ LinearMap.range (relationMap B I)) +
    Module.finrank (ZMod 2) (LinearMap.range (relationMap B I)) =
      Fintype.card V + Fintype.card C at h
  omega

#print axioms relationMap
#print axioms relationMap_apply
#print axioms normal_coordinate
#print axioms remaining_coordinate
#print axioms relationMap_injective
#print axioms relationMap_single
#print axioms quotient_dimension
end Verification.OriginalWittRelationRank
