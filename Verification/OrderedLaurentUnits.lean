/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Group.Basic

/-!
# Ordered Laurent Units

Units of a group algebra over a domain, for a linearly ordered
abelian exponent group, have exactly one monomial. The proof compares
the least and greatest support terms of a unit and its inverse.
-/
noncomputable section
namespace Verification.OrderedLaurentUnits
open Finsupp
variable {R A : Type*} [CommRing R] [IsDomain R]
variable [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
variable (f g : AddMonoidAlgebra R A) (a b : A)

omit [IsDomain R] in
theorem maximal_coefficient
    (ha : ∀ i∈f.support,i≤a) (hb : ∀ i∈g.support,i≤b) :
    (f*g) (a+b)=f a*g b := by
  apply AddMonoidAlgebra.mul_apply_add_eq_mul_of_uniqueAdd
  intro i j hi hj he
  have hia : i=a := by
    by_contra hne
    have hlt := add_lt_add_of_lt_of_le (lt_of_le_of_ne (ha i hi) hne) (hb j hj)
    exact hlt.ne he
  exact ⟨hia,add_left_cancel (hia ▸ he)⟩

theorem maximal_sum_zero (hfg : f*g=1) (ha : a∈f.support) (hb : b∈g.support)
    (hfa : ∀ i∈f.support,i≤a) (hgb : ∀ i∈g.support,i≤b) : a+b=0 := by
  have h : a+b∈(f*g).support := by
    rw [mem_support_iff,maximal_coefficient f g a b hfa hgb]
    exact mul_ne_zero (mem_support_iff.mp ha) (mem_support_iff.mp hb)
  rw [hfg] at h
  change a+b∈(Finsupp.single (0:A) (1:R)).support at h
  by_contra hn
  exact (mem_support_iff.mp h) (Finsupp.single_eq_of_ne (Ne.symm hn))

omit [IsDomain R] in
theorem minimal_coefficient
    (ha : ∀ i∈f.support,a≤i) (hb : ∀ i∈g.support,b≤i) :
    (f*g) (a+b)=f a*g b := by
  apply AddMonoidAlgebra.mul_apply_add_eq_mul_of_uniqueAdd
  intro i j hi hj he
  have hia : i=a := by
    by_contra hne
    have hlt := add_lt_add_of_lt_of_le (lt_of_le_of_ne (ha i hi) (Ne.symm hne)) (hb j hj)
    exact hlt.ne he.symm
  exact ⟨hia,add_left_cancel (hia ▸ he)⟩

theorem minimal_sum_zero (hfg : f*g=1) (ha : a∈f.support) (hb : b∈g.support)
    (hfa : ∀ i∈f.support,a≤i) (hgb : ∀ i∈g.support,b≤i) : a+b=0 := by
  have h : a+b∈(f*g).support := by
    rw [mem_support_iff,minimal_coefficient f g a b hfa hgb]
    exact mul_ne_zero (mem_support_iff.mp ha) (mem_support_iff.mp hb)
  rw [hfg] at h
  change a+b∈(Finsupp.single (0:A) (1:R)).support at h
  by_contra hn
  exact (mem_support_iff.mp h) (Finsupp.single_eq_of_ne (Ne.symm hn))

theorem support_singleton (u : (AddMonoidAlgebra R A)ˣ) :
    ∃ a,(u : AddMonoidAlgebra R A).support={a} := by
  let f : AddMonoidAlgebra R A := u
  let g : AddMonoidAlgebra R A := ↑(u⁻¹)
  have hf : f.support.Nonempty := support_nonempty_iff.mpr u.ne_zero
  have hg : g.support.Nonempty := support_nonempty_iff.mpr (u⁻¹).ne_zero
  let a := f.support.max' hf
  let b := g.support.max' hg
  let c := f.support.min' hf
  let d := g.support.min' hg
  have hab : a+b=0 := maximal_sum_zero f g a b u.val_inv
    (Finset.max'_mem _ _) (Finset.max'_mem _ _)
    (fun i hi => Finset.le_max' _ _ hi) (fun i hi => Finset.le_max' _ _ hi)
  have hcd : c+d=0 := minimal_sum_zero f g c d u.val_inv
    (Finset.min'_mem _ _) (Finset.min'_mem _ _)
    (fun i hi => Finset.min'_le _ _ hi) (fun i hi => Finset.min'_le _ _ hi)
  have hdb : d≤b := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hac : a≤c := (add_le_add_iff_right d).mp
    ((add_le_add_left hdb a).trans_eq (hab.trans hcd.symm))
  refine ⟨a,Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.max'_mem _ _,?_⟩⟩
  intro i hi
  exact le_antisymm (Finset.le_max' _ _ hi) (hac.trans (Finset.min'_le _ _ hi))

theorem unit_monomial (u : (AddMonoidAlgebra R A)ˣ) :
    ∃ (a : A) (c : Rˣ),(u : AddMonoidAlgebra R A)=Finsupp.single a (c : R) := by
  obtain ⟨a,ha⟩ := support_singleton u
  obtain ⟨b,hb⟩ := support_singleton (u⁻¹)
  have hfa : ∀ i∈(u : AddMonoidAlgebra R A).support,i≤a := by
    intro i hi
    rw [ha,Finset.mem_singleton] at hi
    exact hi.le
  have hgb : ∀ i∈(↑(u⁻¹) : AddMonoidAlgebra R A).support,i≤b := by
    intro i hi
    rw [hb,Finset.mem_singleton] at hi
    exact hi.le
  have h := maximal_coefficient (u : AddMonoidAlgebra R A) (↑(u⁻¹)) a b hfa hgb
  have hab := maximal_sum_zero (u : AddMonoidAlgebra R A) (↑(u⁻¹)) a b u.val_inv
    (by rw [ha];exact Finset.mem_singleton_self _) (by rw [hb];exact Finset.mem_singleton_self _) hfa hgb
  have hfg : (u : AddMonoidAlgebra R A)*(↑(u⁻¹) : AddMonoidAlgebra R A)=1 := u.val_inv
  have hu : IsUnit ((u : AddMonoidAlgebra R A) a) := isUnit_of_mul_eq_one _ _ (by
    rw [← h,hfg,hab]
    simp only [AddMonoidAlgebra.one_def,single_eq_same])
  refine ⟨a,hu.unit,?_⟩
  ext i
  by_cases hi : i=a
  · subst i
    rw [single_eq_same,hu.unit_spec]
  · rw [single_eq_of_ne (Ne.symm hi)]
    exact not_mem_support_iff.mp (by rw [ha];simpa using hi)

#print axioms maximal_coefficient
#print axioms maximal_sum_zero
#print axioms minimal_coefficient
#print axioms minimal_sum_zero
#print axioms support_singleton
#print axioms unit_monomial
end Verification.OrderedLaurentUnits
