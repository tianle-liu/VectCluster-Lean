/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenSignFamily
import Verification.ActualSignatureLattice

/-!
# Frozen Sign Terms

Exact cochain coordinates as the original finite family of sign-label
functions, retaining all mutable and frozen coordinates.
-/
noncomputable section
namespace Verification.FrozenSignTerms
open Verification.SignComplex Verification.FrozenSignStates Verification.FrozenSignFamily
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder (V ⊕ C)]
variable (B : (V ⊕ C) → V → ℤ) (F : Finset V → Prop) (p : ℕ)

def Index := {I : Finset V // F I ∧ I.card=p}

def Labels := Σ I : Index F p, ActualSignLabels.labels B I.val

def degreeMap (q : Labels B F p) :
    {s : State (V ⊕ C) // allowed B F s ∧ (holes s).card=p} :=
  ⟨state B q.1.val q.2,state_allowed B F q.1.val q.1.property.1 q.2,
    by rw [state_holes]; exact (Finset.card_map _).trans q.1.property.2⟩

theorem degreeMap_injective : Function.Injective (degreeMap B F p) := by
  rintro ⟨⟨I,hI⟩,ε⟩ ⟨⟨J,hJ⟩,η⟩ h
  have hs : state B I ε=state B J η := congrArg Subtype.val h
  have hIJ : I=J := zeroSet_injective (by rw [← state_holes B I ε,← state_holes B J η,hs])
  subst J
  have hε : ε=η := by
    apply (coordinates B I).symm.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hs
  subst η
  rfl

theorem degreeMap_surjective : Function.Surjective (degreeMap B F p) := by
  intro s
  obtain ⟨q,hq⟩ := labelsToState_surjective B F ⟨s.val,s.property.1⟩
  have hs : state B q.1.val q.2=s.val := congrArg Subtype.val hq
  have hp : q.1.val.card=p := by
    have h := s.property.2
    rw [← hs,state_holes] at h
    simpa only [zeroSet,Finset.card_map] using h
  exact ⟨⟨⟨q.1.val,q.1.property,hp⟩,q.2⟩,Subtype.ext hs⟩

def degreeEquiv : Labels B F p ≃ {s : State (V ⊕ C) // allowed B F s ∧ (holes s).card=p} :=
  Equiv.ofBijective (degreeMap B F p) ⟨degreeMap_injective B F p,degreeMap_surjective B F p⟩

def functionCoordinates :
    ({s : State (V ⊕ C) // allowed B F s ∧ (holes s).card=p} → ℤ) ≃ₗ[ℤ] (Labels B F p → ℤ) where
  toFun f q := f (degreeEquiv B F p q)
  invFun f s := f ((degreeEquiv B F p).symm s)
  left_inv f := by funext s; simp
  right_inv f := by funext q; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def termCoordinates : SignHomology.term (allowed B F) p ≃ₗ[ℤ] (Labels B F p → ℤ) :=
  (SignHomology.coordinates (allowed B F) p).trans (functionCoordinates B F p)

theorem termCoordinates_apply (f : SignHomology.term (allowed B F) p) (q : Labels B F p) :
    termCoordinates B F p f q=f.val ⟨state B q.1.val q.2,state_allowed B F q.1.val q.1.property.1 q.2⟩ := rfl

variable (hAS : ∀ I, F I → AnticliqueSubcolumns.AS B I) (w : ℤ)

def lattice : Submodule ℤ (Labels B F p → ℤ) where
  carrier := {f | ∀ I : Index F p,
    (fun ε => f ⟨I,ε⟩)∈ActualSignatureLattice.lattice B I.val (hAS I.val I.property.1) w}
  zero_mem' := fun I => (ActualSignatureLattice.lattice B I.val (hAS I.val I.property.1) w).zero_mem
  add_mem' hf hg I := (ActualSignatureLattice.lattice B I.val (hAS I.val I.property.1) w).add_mem (hf I) (hg I)
  smul_mem' r _ hf I := (ActualSignatureLattice.lattice B I.val (hAS I.val I.property.1) w).smul_mem r (hf I)

omit [LinearOrder (V ⊕ C)] in
theorem scaled_function_mem (f : Labels B F p → ℤ) :
    (2:ℤ)^((Fintype.card V+Fintype.card C:ℤ)-p-w).toNat • f ∈ lattice B F p hAS w := by
  intro I
  have h := ActualSignatureLattice.scaled_function_mem B I.val (hAS I.val I.property.1) w
    (fun ε => f ⟨I,ε⟩)
  simpa only [I.property.2] using h

omit [LinearOrder (V ⊕ C)] in
theorem lattice_eq_top (hw : (Fintype.card V+Fintype.card C:ℤ)-p≤w) : lattice B F p hAS w=⊤ := by
  apply top_unique
  intro f _
  have h := scaled_function_mem B F p hAS w f
  have he : ((Fintype.card V+Fintype.card C:ℤ)-p-w).toNat=0 := by omega
  simpa only [he,pow_zero,one_smul] using h

#print axioms Index
#print axioms Labels
#print axioms degreeMap
#print axioms degreeMap_injective
#print axioms degreeMap_surjective
#print axioms degreeEquiv
#print axioms functionCoordinates
#print axioms termCoordinates
#print axioms termCoordinates_apply
#print axioms lattice
#print axioms scaled_function_mem
#print axioms lattice_eq_top
end Verification.FrozenSignTerms
