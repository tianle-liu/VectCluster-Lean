/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ComponentCriterion
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Data.Fintype.Powerset

/-!
# Component Row

The full last component-residue matrix has independent images at
distinct target strata. Source coordinates are the integer exponents
indexed by predecessor, missing coordinate, and predecessor component.
Unused coordinates are harmless; every used coordinate is uniquely
assigned to its target. No geometric Chow comparison is assumed here.
-/
noncomputable section
namespace Verification.ComponentRow
open Verification.ComponentCriterion
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : Finset α → Type*)
  (res : ∀ S : Finset α, ∀ i : S, P S → P (S.erase i.val))
  (F : Set (Finset α)) (p : ℕ)

abbrev Target := {J : Finset α // J ∈ F ∧ J.card=p}
noncomputable instance targetFintype : Fintype (Target F p) := Fintype.ofFinite _

abbrev SourceIndex := Σ I : Finset α, α × P I
abbrev FlagIndex := Σ J : Target F p, Σ i : J.val, P (J.val.erase i.val)

def forgetFlag (b : FlagIndex P F p) : SourceIndex P :=
  ⟨b.1.val.erase b.2.1.val,(b.2.1.val,b.2.2)⟩

omit [Fintype α] in
theorem forgetFlag_injective : Function.Injective (forgetFlag P F p) := by
  rintro ⟨J,i,a⟩ ⟨K,j,b⟩ h
  have hi : i.val=j.val := congrArg (fun z : SourceIndex P => z.2.1) h
  have hs : J.val.erase i.val=K.val.erase j.val := congrArg Sigma.fst h
  have hJK : J=K := by
    apply Subtype.ext
    calc J.val = insert i.val (J.val.erase i.val) := (Finset.insert_erase i.property).symm
         _ = insert j.val (K.val.erase j.val) := by rw [hs,hi]
         _ = K.val := Finset.insert_erase j.property
  subst K
  have hij : i=j := Subtype.ext hi
  subst j
  have hab : a=b := by simpa [forgetFlag] using h
  subst b
  rfl

def restriction : (SourceIndex P → ℤ) →ₗ[ℤ]
    (∀ J : Target F p, ∀ i : J.val, P (J.val.erase i.val) → ℤ) where
  toFun x J i c := x (forgetFlag P F p ⟨J,i,c⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype α] in
theorem restriction_surjective : Function.Surjective (restriction P F p) := by
  intro y
  let f : FlagIndex P F p → ℤ := fun z => y z.1 z.2.1 z.2.2
  refine ⟨Function.extend (forgetFlag P F p) f (fun _ => 0),?_⟩
  funext J i c
  exact (forgetFlag_injective P F p).extend_apply f (fun _ => 0) ⟨J,i,c⟩

def blockMap : (∀ J : Target F p, ∀ i : J.val, P (J.val.erase i.val) → ℤ) →ₗ[ℤ]
    (∀ J : Target F p, P J.val → ℤ) :=
  LinearMap.pi (fun J => (jointPullback P res J.val).comp (LinearMap.proj J))

def differential : (SourceIndex P → ℤ) →ₗ[ℤ] (∀ J : Target F p, P J.val → ℤ) :=
  (blockMap P res F p).comp (restriction P F p)

omit [Fintype α] in
theorem differential_apply (x : SourceIndex P → ℤ) (J : Target F p) (c : P J.val) :
    differential P res F p x J c = ∑ i : J.val, x ⟨J.val.erase i.val,(i.val,res J.val i c)⟩ := rfl

omit [Fintype α] in
theorem range_blockMap : LinearMap.range (blockMap P res F p)=
    Submodule.pi Set.univ (fun J : Target F p => LinearMap.range (jointPullback P res J.val)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩ J _
    exact ⟨x J,rfl⟩
  · intro y hy
    have hh : ∀ J : Target F p, ∃ x, jointPullback P res J.val x=y J := fun J => hy J (Set.mem_univ _)
    refine ⟨fun J => (hh J).choose,?_⟩
    funext J
    exact (hh J).choose_spec

omit [Fintype α] in
theorem differential_range : LinearMap.range (differential P res F p)=
    Submodule.pi Set.univ (fun J : Target F p => LinearMap.range (jointPullback P res J.val)) := by
  rw [differential,LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (restriction_surjective P F p)),range_blockMap]

def cokernelEquiv :
    ((∀ J : Target F p, P J.val → ℤ) ⧸ LinearMap.range (differential P res F p)) ≃ₗ[ℤ]
      (∀ J : Target F p, ComponentCokernel P res J.val) := by
  classical
  exact (Submodule.quotEquivOfEq _ _ (differential_range P res F p)).trans
    (Submodule.quotientPi (fun J : Target F p => LinearMap.range (jointPullback P res J.val)))

#print axioms targetFintype
#print axioms forgetFlag
#print axioms forgetFlag_injective
#print axioms restriction
#print axioms restriction_surjective
#print axioms blockMap
#print axioms differential
#print axioms differential_apply
#print axioms range_blockMap
#print axioms differential_range
#print axioms cokernelEquiv
end Verification.ComponentRow

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.ComponentRow.FlagIndex
#print axioms Verification.ComponentRow.SourceIndex
#print axioms Verification.ComponentRow.Target
