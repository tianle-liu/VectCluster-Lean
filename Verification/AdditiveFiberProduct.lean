/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Hom.Instances

/-!
# Additive Fiber Product

A concrete fiber product of additive groups. If the second group and
its common quotient are zero, projection to the first factor is bijective.
The equivalence retains that projection, rather than choosing a new map.
-/
noncomputable section
namespace Verification.AdditiveFiberProduct
variable {H S Q : Type*} [AddCommGroup H] [AddCommGroup S] [AddCommGroup Q]
variable (f : H →+ Q) (g : S →+ Q)

def group : AddSubgroup (H × S) where
  carrier := {x | f x.1 = g x.2}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, map_add] at *
    rw [ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, map_neg] at *
    rw [ha]

def first : group f g →+ H where
  toFun x := x.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem first_bijective [Subsingleton S] [Subsingleton Q] :
    Function.Bijective (first f g) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact Prod.ext hab (Subsingleton.elim _ _)
  · intro h
    exact ⟨⟨(h,0), Subsingleton.elim _ _⟩, rfl⟩

def firstEquiv [Subsingleton S] [Subsingleton Q] : group f g ≃+ H :=
  AddEquiv.ofBijective (first f g) (first_bijective f g)

theorem firstEquiv_apply [Subsingleton S] [Subsingleton Q] (x : group f g) :
    firstEquiv f g x = x.val.1 := rfl

#print axioms group
#print axioms first
#print axioms first_bijective
#print axioms firstEquiv
#print axioms firstEquiv_apply
end Verification.AdditiveFiberProduct
