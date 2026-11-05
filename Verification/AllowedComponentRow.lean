/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ComponentRow
import Verification.PrimeLayerCover

/-!
# Allowed Component Row

The component row with only allowed strata. This avoids inventing
component maps on disallowed strata. Each flag coordinate belongs to a
unique target, so the row image is the product of its target block images.
-/
noncomputable section
namespace Verification.AllowedComponentRow
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Allowed : Finset α → Prop)
variable (hereditary : ∀ J, Allowed J → ∀ v : J, Allowed (J.erase v.val))
variable (p : ℕ)

abbrev Source := Verification.PrimeLayerCover.Index Allowed p
abbrev Target := Verification.PrimeLayerCover.Index Allowed (p+1)

def predecessor (J : Target Allowed p) (v : J.val) : Source Allowed p :=
  ⟨J.val.erase v.val, by
    constructor
    · rw [Finset.card_erase_of_mem v.property, J.property.1]
      omega
    · exact hereditary J.val J.property.2 v⟩

variable (P : Source Allowed p → Type*) (Q : Target Allowed p → Type*)
abbrev SourceIndex := Σ I : Source Allowed p, α × P I
abbrev FlagIndex := Σ J : Target Allowed p, Σ v : J.val, P (predecessor Allowed hereditary p J v)

def forgetFlag (b : FlagIndex Allowed hereditary p P) : SourceIndex Allowed p P :=
  ⟨predecessor Allowed hereditary p b.1 b.2.1, (b.2.1.val, b.2.2)⟩

omit [Fintype α] in
theorem forgetFlag_injective : Function.Injective (forgetFlag Allowed hereditary p P) := by
  rintro ⟨J,v,a⟩ ⟨K,w,b⟩ h
  have hv : v.val = w.val := congrArg (fun z : SourceIndex Allowed p P => z.2.1) h
  have hs : J.val.erase v.val = K.val.erase w.val :=
    congrArg (fun z : SourceIndex Allowed p P => z.1.val) h
  have hJK : J = K := by
    apply Subtype.ext
    calc
      J.val = insert v.val (J.val.erase v.val) := (Finset.insert_erase v.property).symm
      _ = insert w.val (K.val.erase w.val) := by rw [hs, hv]
      _ = K.val := Finset.insert_erase w.property
  subst K
  have hvw : v = w := Subtype.ext hv
  subst w
  have hab : a = b := by simpa [forgetFlag] using h
  subst b
  rfl

def restriction : (SourceIndex Allowed p P → ℤ) →ₗ[ℤ]
    (∀ J : Target Allowed p, ∀ v : J.val, P (predecessor Allowed hereditary p J v) → ℤ) where
  toFun x J v c := x (forgetFlag Allowed hereditary p P ⟨J,v,c⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype α] in
theorem restriction_surjective : Function.Surjective (restriction Allowed hereditary p P) := by
  intro y
  let f : FlagIndex Allowed hereditary p P → ℤ := fun z => y z.1 z.2.1 z.2.2
  refine ⟨Function.extend (forgetFlag Allowed hereditary p P) f (fun _ => 0), ?_⟩
  funext J v c
  exact (forgetFlag_injective Allowed hereditary p P).extend_apply f (fun _ => 0) ⟨J,v,c⟩

variable (res : ∀ J : Target Allowed p, ∀ v : J.val, Q J → P (predecessor Allowed hereditary p J v))

def jointPullback (J : Target Allowed p) :
    (∀ v : J.val, P (predecessor Allowed hereditary p J v) → ℤ) →ₗ[ℤ] (Q J → ℤ) where
  toFun a c := ∑ v : J.val, a v (res J v c)
  map_add' a b := by ext c; exact Finset.sum_add_distrib
  map_smul' z a := by ext c; exact (Finset.mul_sum _ _ _).symm

def blockMap : (∀ J : Target Allowed p, ∀ v : J.val, P (predecessor Allowed hereditary p J v) → ℤ) →ₗ[ℤ]
    (∀ J : Target Allowed p, Q J → ℤ) :=
  LinearMap.pi (fun J => (jointPullback Allowed hereditary p P Q res J).comp (LinearMap.proj J))

def differential : (SourceIndex Allowed p P → ℤ) →ₗ[ℤ] (∀ J : Target Allowed p, Q J → ℤ) :=
  (blockMap Allowed hereditary p P Q res).comp (restriction Allowed hereditary p P)

omit [Fintype α] in
theorem differential_apply (x : SourceIndex Allowed p P → ℤ) (J : Target Allowed p) (c : Q J) :
    differential Allowed hereditary p P Q res x J c =
      ∑ v : J.val, x ⟨predecessor Allowed hereditary p J v, (v.val,res J v c)⟩ := rfl

omit [Fintype α] in
theorem range_blockMap : LinearMap.range (blockMap Allowed hereditary p P Q res) =
    Submodule.pi Set.univ (fun J => LinearMap.range (jointPullback Allowed hereditary p P Q res J)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩ J _
    exact ⟨x J,rfl⟩
  · intro y hy
    have h : ∀ J, ∃ x, jointPullback Allowed hereditary p P Q res J x = y J :=
      fun J => hy J (Set.mem_univ _)
    exact ⟨fun J => (h J).choose, funext (fun J => (h J).choose_spec)⟩

omit [Fintype α] in
theorem differential_range : LinearMap.range (differential Allowed hereditary p P Q res) =
    Submodule.pi Set.univ (fun J => LinearMap.range (jointPullback Allowed hereditary p P Q res J)) := by
  rw [differential, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (restriction_surjective Allowed hereditary p P)), range_blockMap]

def cokernelEquiv :
    ((∀ J : Target Allowed p, Q J → ℤ) ⧸ LinearMap.range (differential Allowed hereditary p P Q res)) ≃ₗ[ℤ]
    (∀ J, (Q J → ℤ) ⧸ LinearMap.range (jointPullback Allowed hereditary p P Q res J)) := by
  classical
  letI : Fintype (Target Allowed p) := Fintype.ofFinite _
  exact (Submodule.quotEquivOfEq _ _ (differential_range Allowed hereditary p P Q res)).trans
    (Submodule.quotientPi _)

#print axioms Source
#print axioms Target
#print axioms predecessor
#print axioms SourceIndex
#print axioms FlagIndex
#print axioms forgetFlag
#print axioms forgetFlag_injective
#print axioms restriction
#print axioms restriction_surjective
#print axioms jointPullback
#print axioms blockMap
#print axioms differential
#print axioms differential_apply
#print axioms range_blockMap
#print axioms differential_range
#print axioms cokernelEquiv
end Verification.AllowedComponentRow
