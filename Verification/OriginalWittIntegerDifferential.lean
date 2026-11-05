/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittQuotient
import Verification.SubsetProjectionComplex

/-!
# Original Witt Integer Differential

The literal signed group-ring cellular differential. Its square is
proved by lifting to the common ambient group ring, where coordinate
projections commute and the ordered incidence signs cancel.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalWittIntegerDifferential
open Verification.OriginalWittQuotient Verification.SignedGroupRingFace
variable {V C : Type*} [Fintype V] [Fintype C] [LinearOrder V]
variable (B : (V ⊕ C) → V → ℤ) (F : Finset V → Prop)
variable (down : ∀ I J, J⊆I → F I → F J)
variable (indep : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0)

abbrev Index (F : Finset V → Prop) := {I : Finset V // F I}
abbrev Cochains := (I : Index F) → Stratum B I.val

def quotient : (Finset V → Ambient V C) →+ Cochains B F where
  toFun f I := Ideal.Quotient.mk _ (f I.val)
  map_zero' := by funext I; exact map_zero _
  map_add' f g := by funext I; exact map_add _ _ _

omit [Fintype V] [Fintype C] [LinearOrder V] in
theorem quotient_surjective : Function.Surjective (quotient B F) := by
  intro f
  choose g hg using fun I : Index F => Ideal.Quotient.mk_surjective (f I)
  refine ⟨fun I => if h : F I then g ⟨I,h⟩ else 0,?_⟩
  funext I
  simp only [quotient,AddMonoidHom.coe_mk,ZeroHom.coe_mk,dif_pos I.property]
  exact hg I

def predecessor (J : Index F) (i : J.val) : Index F :=
  ⟨J.val.erase i.val, down J.val _ (Finset.erase_subset _ _) J.property⟩

omit [Fintype V] [Fintype C] in
include indep in
theorem face_column_zero (J : Index F) (i : J.val) :
    ∀ a : J.val.erase i.val, B (Sum.inl i.val) a.val = 0 := by
  intro a
  exact indep J.val J.property a.val (Finset.mem_of_mem_erase a.property)
    i.val i.property (Finset.ne_of_mem_erase a.property)

def differential : Cochains B F →+ Cochains B F where
  toFun f J := ∑ i : J.val, SubsetProjectionComplex.sign J.val i.val •
    residue B (J.val.erase i.val) J.val i.val (Finset.erase_subset _ _)
      (Finset.not_mem_erase _ _) (face_column_zero B F indep J i)
      (f (predecessor F down J i))
  map_zero' := by funext J; simp
  map_add' f g := by funext J; simp [map_add,smul_add,Finset.sum_add_distrib]

def rawDifferential : (Finset V → Ambient V C) → (Finset V → Ambient V C) :=
  SubsetProjectionComplex.differential (fun i => (projection (coordinate (C := C) i)).toAddMonoidHom)

omit [Fintype C] in
theorem raw_squared (f : Finset V → Ambient V C) : rawDifferential (rawDifferential f) = 0 := by
  funext J
  apply SubsetProjectionComplex.differential_squared
  intro i j a
  exact projections_commute (coordinate i) (coordinate j) a

omit [Fintype C] in
theorem differential_lift (f : Finset V → Ambient V C) :
    differential B F down indep (quotient B F f) = quotient B F (rawDifferential f) := by
  funext J
  change (∑ i : J.val, _ ) = Ideal.Quotient.mk _ (rawDifferential f J.val)
  rw [rawDifferential,SubsetProjectionComplex.differential_formula,
    ← Finset.sum_coe_sort J.val,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change SubsetProjectionComplex.sign J.val i.val •
      residue B _ _ _ _ _ _ (Ideal.Quotient.mk _ (f (J.val.erase i.val))) = _
  rw [residue_mk,map_zsmul]
  rfl

omit [Fintype C] in
theorem differential_squared (f : Cochains B F) :
    differential B F down indep (differential B F down indep f) = 0 := by
  obtain ⟨g,rfl⟩ := quotient_surjective B F f
  rw [differential_lift,differential_lift,raw_squared,map_zero]

omit [Fintype V] [Fintype C] in
theorem degree_preserved (p : ℕ) (f : Cochains B F)
    (hf : ∀ I : Index F, I.val.card ≠ p → f I = 0) :
    ∀ J : Index F, J.val.card ≠ p+1 → differential B F down indep f J = 0 := by
  intro J hJ
  apply Finset.sum_eq_zero
  intro i _
  have hc : (predecessor F down J i).val.card ≠ p := by
    have h := Finset.card_erase_add_one i.property
    change (J.val.erase i.val).card ≠ p
    omega
  rw [hf _ hc,map_zero,smul_zero]

#print axioms Index
#print axioms Cochains
#print axioms quotient
#print axioms quotient_surjective
#print axioms predecessor
#print axioms face_column_zero
#print axioms differential
#print axioms rawDifferential
#print axioms raw_squared
#print axioms differential_lift
#print axioms differential_squared
#print axioms degree_preserved
end Verification.OriginalWittIntegerDifferential
