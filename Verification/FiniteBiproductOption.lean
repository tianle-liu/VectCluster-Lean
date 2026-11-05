/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fintype.Option

/-!
# Finite Biproduct Option

A distinguished zero-weight summand and a finite positive-weight sum
are the actual biproduct indexed by an option type.
-/
noncomputable section
namespace Verification.FiniteBiproductOption
open Classical CategoryTheory CategoryTheory.Limits
variable {A : Type*} [Category A] [Preadditive A] [HasFiniteBiproducts A] [HasBinaryBiproducts A]
variable {I : Type} [Fintype I] (Z : A) (f : I→A)

def family : Option I→A
  | none=>Z
  | some i=>f i

def iso : Z⊞(⨁ f) ≅ ⨁ family Z f where
  hom := biprod.desc (biproduct.ι (family Z f) none)
    (biproduct.desc (fun i=>biproduct.ι (family Z f) (some i)))
  inv := biproduct.desc (fun i=>match i with
    | none=>biprod.inl
    | some i=>biproduct.ι f i≫biprod.inr)
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp; rfl
    · apply biproduct.hom_ext'
      intro i
      simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro i
    cases i <;> simp [Category.assoc]

#print axioms family
#print axioms iso
end Verification.FiniteBiproductOption
