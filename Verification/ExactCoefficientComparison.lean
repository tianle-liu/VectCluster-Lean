/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Exact

/-!
# Exact Coefficient Comparison

Elementary diagram-free consequences of an actual coefficient long
exact sequence. All maps are retained, including the connecting map.
-/
namespace Verification.ExactCoefficientComparison
variable {A B C D E : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
variable (a : A →+ B) (b : B →+ C) (c : C →+ D) (d : D →+ E)

theorem connecting_zero_of_surjective (hab : Function.Exact a b) (ha : Function.Surjective a) :
    b = 0 := by
  ext y
  obtain ⟨x,rfl⟩ := ha y
  exact (hab (a x)).mpr ⟨x,rfl⟩

theorem bijective_of_zero_ends (hbc : Function.Exact b c) (hcd : Function.Exact c d)
    (hb : b = 0) (hd : d = 0) : Function.Bijective c := by
  constructor
  · intro x y hxy
    have hz : c (x-y) = 0 := by rw [map_sub,hxy,sub_self]
    obtain ⟨z,hz'⟩ := (hbc (x-y)).mp hz
    apply sub_eq_zero.mp
    rw [← hz',hb]
    rfl
  · intro y
    exact (hcd y).mp (by rw [hd]; rfl)

#print axioms connecting_zero_of_surjective
#print axioms bijective_of_zero_ends
end Verification.ExactCoefficientComparison
