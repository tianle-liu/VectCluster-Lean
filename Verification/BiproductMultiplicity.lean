/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteMultiplicity
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Biproduct Multiplicity

Reindexing an actual finite categorical biproduct by its value, with
literal fiber cardinalities. Only the finite image is summed over.
-/
noncomputable section
namespace Verification.BiproductMultiplicity
open CategoryTheory CategoryTheory.Limits
open scoped Classical
attribute [local instance] Abelian.hasFiniteBiproducts
variable {ι : Type} [Fintype ι] (g : ι → ℕ)

instance valuesFintype : Fintype (Set.range g) := (Set.finite_range g).fintype

def rangeFiberEquiv : (Σ m : Set.range g, {i : ι // g i=m.val}) ≃ ι where
  toFun x := x.2.val
  invFun i := ⟨⟨g i,⟨i,rfl⟩⟩,⟨i,rfl⟩⟩
  left_inv := by
    rintro ⟨⟨m,hm⟩,i,hi⟩
    change g i=m at hi
    subst m
    rfl
  right_inv _ := rfl

def groupedIndex : ι ≃ Σ m : Set.range g, Fin (FiniteMultiplicity.multiplicity g m.val) :=
  (rangeFiberEquiv g).symm.trans
    (Equiv.sigmaCongrRight fun m => Fintype.equivFin {i : ι // g i=m.val})

theorem groupedIndex_value (i : ι) : (groupedIndex g i).1.val = g i := rfl

variable {C : Type*} [Category C] [Abelian C] (M : ℕ → C)

def groupedIso : (⨁ fun i : ι => M (g i)) ≅
    ⨁ fun m : Set.range g => ⨁ fun _ : Fin (FiniteMultiplicity.multiplicity g m.val) => M m.val :=
  biproduct.whiskerEquiv (groupedIndex g) (fun i => eqToIso (congrArg M (groupedIndex_value g i))) ≪≫
    (biproductBiproductIso (fun m : Set.range g => Fin (FiniteMultiplicity.multiplicity g m.val))
      (fun m _ => M m.val)).symm

#print axioms valuesFintype
#print axioms rangeFiberEquiv
#print axioms groupedIndex
#print axioms groupedIndex_value
#print axioms groupedIso
end Verification.BiproductMultiplicity
