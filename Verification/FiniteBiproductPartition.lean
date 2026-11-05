/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite Biproduct Partition

Canonical partition of a finite biproduct, keeping the two projections
explicit for later differential comparisons.
-/
noncomputable section
namespace Verification.FiniteBiproductPartition
open Classical CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable {ι : Type} [Fintype ι] (f : ι → C) (p : ι → Prop)

def split : (⨁ f) ≅ (⨁ Subtype.restrict p f) ⊞ (⨁ Subtype.restrict (fun i=>¬p i) f) where
  hom := biprod.lift (biproduct.toSubtype f p) (biproduct.toSubtype f (fun i=>¬p i))
  inv := biprod.desc (biproduct.fromSubtype f p) (biproduct.fromSubtype f (fun i=>¬p i))
  hom_inv_id := by
    apply biproduct.hom_ext
    intro i
    by_cases hi : p i <;> simp [biprod.lift_desc,Category.assoc,hi]
  inv_hom_id := by
    apply biprod.hom_ext
    · apply biproduct.hom_ext
      intro i
      apply biprod.hom_ext'
      · simp [Category.assoc,i.property]
      · simp [Category.assoc,biproduct.fromSubtype_π,i.property]
    · apply biproduct.hom_ext
      intro i
      apply biprod.hom_ext'
      · simp [Category.assoc,biproduct.fromSubtype_π,i.property]
      · simp [Category.assoc,i.property]

theorem fst : (split f p).hom ≫ biprod.fst=(biproduct.toSubtype f p) := by
  simp [split]
theorem snd : (split f p).hom ≫ biprod.snd=(biproduct.toSubtype f (fun i=>¬p i)) := by
  simp [split]
#print axioms split
#print axioms fst
#print axioms snd
end Verification.FiniteBiproductPartition
